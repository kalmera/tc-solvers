From Stdlib Require Import List Bool Lia Arith.PeanoNat Sorting.Permutation Sorting.Sorted Arith.Wf_nat Relations.Relation_Operators Wellfounded.Inverse_Image Wellfounded.Lexicographic_Product.
From TcSolvers Require Import common.Assumptions common.ConstraintSemantics
  common.SolverSpecifications common.SourceStrictness
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.restarting_compact.Restarting.

Import ListNotations.
Set Implicit Arguments.

(** Independent proofs for the unchanged copy of Restarting.  This unit does
    not import any of the reference solver's proofs.  State facts, execution
    reasoning, and the public results share a single machine instance. *)
Module Make (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Ranks : DISCOVERY_ORDER V)
  (Features : Restarting.FEATURES)
  (RL : STABLE_DISCOVERY_ORDER_LAWS V Ranks)
  (RF : FINITE_DISCOVERY_ORDER_LAWS V Ranks RL)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

Module R := Restarting.Make V D U S M Ranks Features.
Module Syntax.
  Definition rhs := R.ConstraintSystem.rhs.
  Definition Ret := R.ConstraintSystem.Ret.
  Definition Get := R.ConstraintSystem.Get.
  Definition Side := R.ConstraintSystem.Side.
  Definition Spawn := R.ConstraintSystem.Spawn.
  Definition system := V.t -> rhs.
End Syntax.
Module Sem := ConstraintSemantics.Make V D Syntax.
Module Transfer.
  Definition rhs := Syntax.rhs.
  Definition observation := Sem.observation.
  Definition observed_sides := Sem.observed_sides.
  Definition observed_spawns := Sem.observed_spawns.
  Definition observes_at := Sem.observes_at.
  Definition rhs_observes := Sem.rhs_observes.
  Definition rhs_eval_with := Sem.rhs_eval_with.
  Definition rhs_dependencies_monotone := Sem.rhs_dependencies_monotone.
  Definition rhs_effects_monotone := Sem.rhs_effects_monotone.
End Transfer.
Module Store.
  Definition state := R.state.
  Definition sigma := R.sigma.
  Definition sigma_value := R.sigma_value.
End Store.
Module Spec := SolverSpecifications.Make V D M Transfer Store.
Include Spec.

Definition step tf before after := R.next_config tf before = Some after.
Inductive steps tf : R.config -> R.config -> Prop :=
| steps_refl c : steps tf c c
| steps_cons before next after :
    step tf before next -> steps tf next after -> steps tf before after.

Definition quiescent st := R.queue st = [].
Definition terminal st : R.config :=
  {| R.cfg_state := st; R.cfg_control := R.RunLoop |}.
Definition terminates_to tf roots final :=
  steps tf (R.initial_config roots) (terminal final) /\ quiescent final.

Lemma steps_append tf a b c : steps tf a b -> steps tf b c -> steps tf a c.
Proof. intros Hab Hbc; induction Hab; eauto using steps. Qed.
Lemma steps_snoc tf a b c : steps tf a b -> step tf b c -> steps tf a c.
Proof. intros Hab Hbc; eapply steps_append; eauto using steps. Qed.
Lemma fuel_path fuel tf c : steps tf c (R.run_fuel fuel tf c).
Proof.
  revert c; induction fuel; intros c; cbn; [constructor |].
  destruct (R.next_config tf c) eqn:Hnext; eauto using steps.
Qed.
Lemma path_fuel tf a b : steps tf a b -> exists fuel, R.run_fuel fuel tf a = b.
Proof.
  intro H; induction H as [a |a next b Hnext Htail [fuel Hfuel]].
  - exists 0; reflexivity.
  - exists (S fuel); cbn; unfold step in Hnext; now rewrite Hnext.
Qed.
Lemma final_shape fuel tf roots final :
  R.solve_fuel fuel tf roots = Some final ->
  R.run_fuel fuel tf (R.initial_config roots) = terminal final /\ quiescent final.
Proof.
  unfold R.solve_fuel; destruct (R.run_fuel fuel tf (R.initial_config roots))
    as [st ctrl]; destruct ctrl; cbn; try discriminate.
  destruct (R.queue st) eqn:Hqueue; cbn; try discriminate.
  intro H; inversion H; subst; split; [reflexivity |exact Hqueue].
Qed.
Lemma successful_path fuel tf roots final :
  R.solve_fuel fuel tf roots = Some final -> terminates_to tf roots final.
Proof.
  intro H; destruct (@final_shape fuel tf roots final H) as [Hshape Hqueue]; split; auto.
  rewrite <- Hshape; apply fuel_path.
Qed.

Definition eqv x y := D.leq x y = true /\ D.leq y x = true.
Lemma eqv_refl x : eqv x x.
Proof. split; apply DL.leq_refl. Qed.
Lemma eqv_sym x y : eqv x y -> eqv y x.
Proof. unfold eqv; tauto. Qed.
Lemma eqv_trans x y z : eqv x y -> eqv y z -> eqv x z.
Proof. intros [Hxy Hyx] [Hyz Hzy]; split; eapply DL.leq_trans; eauto. Qed.
Lemma eqv_bool x y : R.equivalent x y = true <-> eqv x y.
Proof. unfold R.equivalent, eqv; apply andb_true_iff. Qed.
Lemma join_mono x x' y y' :
  D.leq x x' = true -> D.leq y y' = true ->
  D.leq (D.join x y) (D.join x' y') = true.
Proof.
  intros; apply DL.join_least; eapply DL.leq_trans;
    eauto using DL.join_upper_left, DL.join_upper_right.
Qed.
Lemma join_eqv x x' y y' :
  eqv x x' -> eqv y y' -> eqv (D.join x y) (D.join x' y').
Proof. intros [Hxx' Hx'x] [Hyy' Hy'y]; split; apply join_mono; auto. Qed.
Lemma join_bottom x : eqv (D.join D.bottom x) x.
Proof. split; auto using DL.join_upper_right, DL.join_least, DL.bottom_least, DL.leq_refl. Qed.
Lemma fold_bound values upper :
  D.leq (R.join_values values) upper = true <->
  forall value, In value values -> D.leq value upper = true.
Proof.
  induction values as [|v values IH]; cbn.
  - split; [intros _ ? H; contradiction |intros _; apply DL.bottom_least].
  - split.
    + intros H value [<-|Hin].
      * eapply DL.leq_trans; [apply DL.join_upper_left |exact H].
      * apply (proj1 IH); [|exact Hin].
        eapply DL.leq_trans; [apply DL.join_upper_right |exact H].
    + intro H; apply DL.join_least; [apply H; auto |apply IH; intros; apply H; auto].
Qed.
Lemma folded_member value values : In value values -> D.leq value (R.join_values values) = true.
Proof. apply (proj1 (fold_bound values (R.join_values values))), DL.leq_refl. Qed.
Lemma fold_permutation xs ys : Permutation xs ys -> eqv (R.join_values xs) (R.join_values ys).
Proof.
  intro Hperm; split; apply fold_bound; intros value Hin; apply folded_member.
  - eapply Permutation_in; eauto.
  - eapply Permutation_in; [apply Permutation_sym; exact Hperm |exact Hin].
Qed.
Lemma row_lookup {A} (rows : M.t (M.t A)) outer inner value :
  M.lookup (R.lookup_map (R.update_map rows outer inner value) outer) inner = Some value.
Proof. unfold R.update_map, R.lookup_map; now rewrite !ML.lookup_update_same. Qed.
Lemma row_other {A} (rows : M.t (M.t A)) outer inner value observed :
  observed <> outer ->
  R.lookup_map (R.update_map rows outer inner value) observed = R.lookup_map rows observed.
Proof. intro H; unfold R.update_map, R.lookup_map; now rewrite ML.lookup_update_other. Qed.
Lemma contribution_below_aggregate st source target :
  D.leq (R.stored_contribution st source target) (R.aggregate st target) = true.
Proof.
  unfold R.stored_contribution, R.aggregate.
  destruct (M.lookup (R.lookup_map (R.contributions st) target) source) eqn:Hlookup;
    [|apply DL.bottom_least].
  apply folded_member.
  eapply ML.lookup_values; eauto.
Qed.

(** One symbolic case split per primitive, instead of separately traversing
    the same branches for each unchanged record field. Select a match before
    its branch guards so irrelevant branches do not duplicate the proof. *)
Ltac split_program H :=
  repeat match type of H with
  | context [match ?p with _ => _ end] => destruct p eqn:?
  | context [if ?b then _ else _] => destruct b eqn:?
  end; inversion H; subst; clear H.

Record commit_view before fr after next_fr := {
  commit_owner : R.frame_owner next_fr = R.frame_owner fr;
  commit_ranking : R.ranking after = R.ranking before;
  commit_controlled : R.controlled after = R.controlled before;
  commit_contributions : R.contributions after = R.contributions before;
  commit_cells : R.side_cells after = R.side_cells before;
  commit_resets : R.reset_at_close after = R.reset_at_close before;
  commit_targets : R.last_targets after = R.last_targets before;
  commit_other : forall owner, owner <> R.frame_owner fr ->
    M.lookup (R.sigma after) owner = M.lookup (R.sigma before) owner
}.
Lemma commit_footprint st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) -> commit_view st fr next next_fr.
Proof.
  unfold R.set_value; intro H; split_program H; constructor;
    cbn; auto using ML.lookup_update_other.
Qed.
Lemma commit_sound st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) ->
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr)))
    (R.sigma_value next (R.frame_owner fr)) = true.
Proof.
  unfold R.set_value; intro H.
  destruct (R.equivalent _ _) eqn:Hcandidate.
  - inversion H; subst next next_fr; exact (proj1 (proj1 (eqv_bool _ _) Hcandidate)).
  - destruct (S.mem _ _) eqn:Hcontrolled.
    + destruct (U.update _ _ _ _ _) as [phase value] eqn:Hupdate; cbn in H.
      pose proof (@UL.update_sound false (R.frame_owner fr) (R.frame_phase fr)
        (R.sigma_value st (R.frame_owner fr))
        (D.join direct (R.aggregate st (R.frame_owner fr)))) as Hsound.
      rewrite Hupdate in Hsound; cbn in Hsound.
      destruct (R.equivalent value (R.sigma_value st (R.frame_owner fr))) eqn:Hvalue; inversion H; subst next next_fr.
      * eapply DL.leq_trans; [exact Hsound |exact (proj1 (proj1 (eqv_bool _ _) Hvalue))].
      * unfold R.sigma_value; cbn; rewrite ML.lookup_update_same; exact Hsound.
    + cbn in H; rewrite Hcandidate in H; inversion H; subst next next_fr.
      unfold R.sigma_value; cbn; rewrite ML.lookup_update_same; apply DL.leq_refl.
Qed.
Lemma commit_credit st fr direct next next_fr :
  S.mem (R.frame_owner fr) (R.controlled st) = true ->
  R.set_value st fr direct = (next,next_fr) ->
  UL.remaining_changes (R.frame_phase next_fr) (R.sigma_value next (R.frame_owner fr)) <=
    UL.remaining_changes (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr)).
Proof.
  intros Hcontrolled; unfold R.set_value.
  destruct (R.equivalent _ _) eqn:Hcandidate; [intro H; inversion H; subst next next_fr; lia |].
  rewrite Hcontrolled.
  destruct (U.update _ _ _ _ _) as [phase value] eqn:Hupdate; cbn.
  pose proof (@UL.remaining_changes_nonincreasing false (R.frame_owner fr)
    (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
    (D.join direct (R.aggregate st (R.frame_owner fr)))) as Hcredit.
  rewrite Hupdate in Hcredit; cbn in Hcredit.
  destruct (R.equivalent value (R.sigma_value st (R.frame_owner fr))) eqn:Hvalue; intro H; inversion H; subst next next_fr; cbn.
  - rewrite (@UL.remaining_changes_extensional phase value
      (R.sigma_value st (R.frame_owner fr)) (proj1 (eqv_bool _ _) Hvalue)) in Hcredit.
    exact Hcredit.
  - unfold R.sigma_value; cbn; rewrite ML.lookup_update_same; exact Hcredit.
Qed.
Lemma commit_credit_strict st fr direct next next_fr :
  S.mem (R.frame_owner fr) (R.controlled st) = true ->
  R.set_value st fr direct = (next,next_fr) ->
  R.equivalent (R.sigma_value next (R.frame_owner fr))
    (R.sigma_value st (R.frame_owner fr)) = false ->
  UL.remaining_changes (R.frame_phase next_fr) (R.sigma_value next (R.frame_owner fr)) <
    UL.remaining_changes (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr)).
Proof.
  intros Hcontrolled; unfold R.set_value.
  destruct (R.equivalent _ _) eqn:Hcandidate.
  - intros H; inversion H; subst next next_fr; rewrite (proj2 (eqv_bool _ _) (eqv_refl _)); discriminate.
  - rewrite Hcontrolled; destruct (U.update _ _ _ _ _) as [phase value] eqn:Hupdate; cbn.
    destruct (R.equivalent value (R.sigma_value st (R.frame_owner fr))) eqn:Hvalue; intros H; inversion H; subst next next_fr.
    + rewrite (proj2 (eqv_bool _ _) (eqv_refl _)); discriminate.
    + intros _; pose proof (@UL.update_change_consumes false (R.frame_owner fr)
        (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
        (D.join direct (R.aggregate st (R.frame_owner fr)))) as Hcredit.
      rewrite Hupdate in Hcredit; cbn in Hcredit.
      unfold R.sigma_value; cbn; rewrite ML.lookup_update_same; apply Hcredit.
      intro Heq; apply (proj2 (eqv_bool _ _)) in Heq; congruence.
Qed.

(** Queue membership is independent of the ranking policy; order facts only
    need the policy's stable, injective partial order. *)
Lemma contains_spec x queue : R.queue_contains x queue = true <-> In x queue.
Proof.
  induction queue as [|head tail IH]; cbn; [split; [discriminate |contradiction] |].
  destruct (V.eq_dec x head); [subst; intuition |rewrite IH; intuition congruence].
Qed.
Lemma fresh_members order x queue y :
  In y (R.queue_insert_fresh order x queue) <-> y = x \/ In y queue.
Proof.
  induction queue as [|head tail IH]; cbn; [intuition |].
  destruct (R.ranking_lt order head x); cbn; [intuition |rewrite IH; intuition congruence].
Qed.
Lemma insert_members order x queue y :
  In y (R.queue_insert order x queue) <-> y = x \/ In y queue.
Proof.
  unfold R.queue_insert; destruct (R.queue_contains x queue) eqn:Hcontains;
    [apply contains_spec in Hcontains; intuition congruence |apply fresh_members].
Qed.
Lemma insert_all_members order xs queue y :
  In y (R.queue_insert_all order xs queue) <-> In y xs \/ In y queue.
Proof.
  revert queue; induction xs as [|x xs IH]; intros queue; cbn; [tauto |].
  rewrite IH, insert_members; intuition congruence.
Qed.
Lemma fresh_distinct order x queue :
  NoDup queue -> ~ In x queue -> NoDup (R.queue_insert_fresh order x queue).
Proof.
  induction queue as [|head tail IH]; intros Hq Hfresh; cbn.
  - constructor; [tauto |constructor].
  - inversion Hq; subst; destruct (R.ranking_lt order head x); cbn.
    + constructor; assumption.
    + constructor.
      * rewrite fresh_members; intros [->|Hin]; [apply Hfresh; now left |contradiction].
      * apply IH; auto; intro H; apply Hfresh; now right.
Qed.
Lemma insert_distinct order x queue : NoDup queue -> NoDup (R.queue_insert order x queue).
Proof.
  intro Hq; unfold R.queue_insert; destruct (R.queue_contains x queue) eqn:Hcontains; auto.
  apply fresh_distinct; auto; intro Hin; apply contains_spec in Hin; congruence.
Qed.
Lemma insert_all_distinct order xs queue :
  NoDup queue -> NoDup (R.queue_insert_all order xs queue).
Proof. revert queue; induction xs; cbn; eauto using insert_distinct. Qed.
Lemma enqueue_members st x y : In y (R.queue (R.enqueue st x)) <-> y = x \/ In y (R.queue st).
Proof. apply insert_members. Qed.
Lemma requeue_members before after x y :
  In y (R.queue (R.requeue_changed_controlled_owner before after x)) ->
  y = x \/ In y (R.queue after).
Proof.
  unfold R.requeue_changed_controlled_owner; cbn; destruct (_ && _)%bool;
    [apply insert_members |tauto].
Qed.
Lemma requeue_if_changed before after owner :
  Features.recompute_controlled = true ->
  S.mem owner (R.controlled before) = true ->
  R.equivalent (R.sigma_value after owner) (R.sigma_value before owner) = false ->
  In owner (R.queue (R.requeue_changed_controlled_owner before after owner)).
Proof.
  intros Hon Hcontrolled Hchanged; unfold R.requeue_changed_controlled_owner;
    rewrite Hon, Hcontrolled, Hchanged; cbn; apply insert_members; auto.
Qed.
Lemma requeue_off before after owner : Features.recompute_controlled = false ->
  R.requeue_changed_controlled_owner before after owner = after.
Proof. intro H; unfold R.requeue_changed_controlled_owner; rewrite H; destruct after; reflexivity. Qed.

Definition ranked order x := exists rank, Ranks.lookup order x = Some rank.
Definition extends order next := forall x rank,
  Ranks.lookup order x = Some rank -> Ranks.lookup next x = Some rank.
Lemma extends_refl order : extends order order.
Proof. firstorder. Qed.
Lemma extends_trans a b c : extends a b -> extends b c -> extends a c.
Proof. unfold extends; eauto. Qed.
Lemma extends_ranked a b : extends a b -> forall x, ranked a x -> ranked b x.
Proof. intros Hab x [rank Hrank]; exists rank; auto. Qed.
Lemma lt_ranks order x y : R.ranking_lt order x y = true ->
  exists rx ry, Ranks.lookup order x = Some rx /\ Ranks.lookup order y = Some ry /\ rx < ry.
Proof.
  unfold R.ranking_lt; destruct (Ranks.lookup order x) eqn:Hx;
    destruct (Ranks.lookup order y) eqn:Hy; try discriminate.
  intro H; apply Nat.ltb_lt in H; eauto.
Qed.
Lemma lt_stable a b x y : extends a b -> ranked a x -> ranked a y ->
  R.ranking_lt b x y = R.ranking_lt a x y.
Proof. intros Hab [rx Hx] [ry Hy]; unfold R.ranking_lt; now rewrite (Hab _ _ Hx), (Hab _ _ Hy), Hx, Hy. Qed.
Lemma lt_irrefl order x : R.ranking_lt order x x = false.
Proof. unfold R.ranking_lt; destruct (Ranks.lookup order x); auto using Nat.ltb_irrefl. Qed.
Lemma lt_trans order x y z :
  R.ranking_lt order x y = true -> R.ranking_lt order y z = true ->
  R.ranking_lt order x z = true.
Proof.
  intros Hxy Hyz; destruct (@lt_ranks order x y Hxy) as [rx [ry [Hx [Hy Hxy']]]];
    destruct (@lt_ranks order y z Hyz) as [ry' [rz [Hy' [Hz Hyz']]]].
  rewrite Hy in Hy'; inversion Hy'; subst; unfold R.ranking_lt;
    rewrite Hx, Hz; apply Nat.ltb_lt; lia.
Qed.
Lemma lt_compare order x y : RL.valid order -> ranked order x -> ranked order y -> x <> y ->
  R.ranking_lt order x y = true \/ R.ranking_lt order y x = true.
Proof.
  intros Hvalid [rx Hx] [ry Hy] Hneq.
  assert (rx <> ry) by (intro H; subst; apply Hneq; eapply RL.lookup_injective; eauto).
  unfold R.ranking_lt; rewrite Hx, Hy; destruct (Nat.lt_trichotomy rx ry);
    [left |destruct H0; [contradiction |right]]; apply Nat.ltb_lt; auto.
Qed.
Lemma observe_order st x :
  extends (R.ranking st) (R.ranking (R.observe st x)) /\
  ranked (R.ranking (R.observe st x)) x /\
  (RL.valid (R.ranking st) -> RL.valid (R.ranking (R.observe st x))).
Proof.
  unfold R.observe; destruct (Ranks.observe (R.ranking st) x) as [order rank] eqn:H; cbn.
  split; [intros y ry Hy; eapply RL.observe_preserves; eauto |].
  split; [exists rank; eapply RL.observe_lookup; eauto |intro Hv; eapply RL.observe_valid; eauto].
Qed.
Definition ordered order queue := StronglySorted (fun x y => R.ranking_lt order y x = true) queue.
Lemma ordered_tail order x xs : ordered order (x::xs) ->
  ordered order xs /\ Forall (fun y => R.ranking_lt order y x = true) xs.
Proof. intro H; inversion H; auto. Qed.
Lemma fresh_ordered order x queue :
  RL.valid order -> ranked order x -> Forall (ranked order) queue ->
  ordered order queue -> ~ In x queue -> ordered order (R.queue_insert_fresh order x queue).
Proof.
  intros Hvalid Hx; induction queue as [|head tail IH]; intros Hr Hq Hfresh; cbn.
  - constructor; constructor.
  - inversion Hr as [|? ? Hhead Htail]; inversion Hq as [|? ? Hsorted Hbelow]; subst.
    rewrite Forall_forall in Hbelow.
    assert (Hneq : x <> head) by (intro H; subst; apply Hfresh; now left).
    destruct (R.ranking_lt order head x) eqn:Hlt.
    + constructor; [exact Hq |constructor; auto].
      apply Forall_forall; intros y Hin.
      eapply lt_trans; [apply Hbelow; exact Hin |exact Hlt].
    + constructor.
      * apply IH; auto; intro Hin; apply Hfresh; now right.
      * apply Forall_forall; intros y Hin; apply fresh_members in Hin; destruct Hin as [->|Hin].
        -- destruct (@lt_compare order x head Hvalid Hx Hhead Hneq); congruence.
        -- apply Hbelow; exact Hin.
Qed.
Lemma insert_ordered order x queue :
  RL.valid order -> ranked order x -> Forall (ranked order) queue ->
  ordered order queue -> ordered order (R.queue_insert order x queue).
Proof.
  intros Hv Hx Hr Hq; unfold R.queue_insert; destruct (R.queue_contains x queue) eqn:Hcontains; auto.
  apply fresh_ordered; auto; intro Hin; apply contains_spec in Hin; congruence.
Qed.

(** A predicate on references is reusable for finite support and for ranks.
    Payload predicates make nested maps and reset registrations uniform. *)
Definition map_ok {A} (keys : V.t -> Prop) (values : A -> Prop) (m : M.t A) :=
  forall key value, M.lookup m key = Some value -> keys key /\ values value.
Definition set_ok (P : V.t -> Prop) values := forall x, S.mem x values = true -> P x.
Definition option_ok (P : V.t -> Prop) value := match value with Some x => P x |None => True end.
Definition pair_ok (P : V.t -> Prop) (pair : V.t * V.t) := P (fst pair) /\ P (snd pair).
Lemma map_empty {A} P Q : @map_ok A P Q (M.empty A).
Proof. intros x value H; rewrite ML.lookup_empty in H; discriminate. Qed.
Lemma map_put {A} P Q (m : M.t A) key value :
  map_ok P Q m -> P key -> Q value -> map_ok P Q (M.update m key value).
Proof.
  intros Hm Hkey Hvalue x v Hlookup; destruct (V.eq_dec x key) as [->|Hneq].
  - rewrite ML.lookup_update_same in Hlookup; inversion Hlookup; subst; auto.
  - rewrite ML.lookup_update_other in Hlookup by exact Hneq; apply Hm; auto.
Qed.
Lemma map_weaken {A} P P' Q Q' (m : M.t A) :
  (forall x, P x -> P' x) -> (forall v, Q v -> Q' v) ->
  map_ok P Q m -> map_ok P' Q' m.
Proof. firstorder. Qed.
Lemma set_empty P : set_ok P S.empty.
Proof. intros x H; rewrite SL.empty_spec in H; discriminate. Qed.
Lemma set_add P values x : set_ok P values -> P x -> set_ok P (S.add x values).
Proof.
  intros Hs Hx y Hy; apply SL.add_spec in Hy; destruct Hy as [->|Hy]; auto.
Qed.
Lemma set_elements P values : set_ok P values <-> Forall P (S.elements values).
Proof. rewrite Forall_forall; unfold set_ok; setoid_rewrite <- SL.mem_spec; reflexivity. Qed.
Lemma lookup_row {A} P Q (rows : M.t (M.t A)) outer :
  map_ok P (map_ok P Q) rows -> map_ok P Q (R.lookup_map rows outer).
Proof.
  intro H; unfold R.lookup_map; destruct (M.lookup rows outer) eqn:Hlookup;
    [exact (proj2 (H _ _ Hlookup)) |apply map_empty].
Qed.
Lemma put_row {A} P Q (rows : M.t (M.t A)) outer inner value :
  map_ok P (map_ok P Q) rows -> P outer -> P inner -> Q value ->
  map_ok P (map_ok P Q) (R.update_map rows outer inner value).
Proof. intros; unfold R.update_map; apply map_put; auto; apply map_put; auto using lookup_row. Qed.
Record references P st := {
  refs_sigma : map_ok P (fun _ => True) (R.sigma st);
  refs_queue : Forall P (R.queue st);
  refs_readers : map_ok P (set_ok P) (R.readers st);
  refs_contributions : map_ok P (map_ok P (fun _ => True)) (R.contributions st);
  refs_cells : map_ok P (map_ok P (fun cell => option_ok P (R.side_reset_at cell))) (R.side_cells st);
  refs_resets : map_ok P (Forall (pair_ok P)) (R.reset_at_close st);
  refs_targets : map_ok P (set_ok P) (R.last_targets st);
  refs_controlled : set_ok P (R.controlled st)
}.
Lemma references_empty P : references P R.empty_state.
Proof. constructor; cbn; auto using map_empty, set_empty, Forall. Qed.
Lemma references_sigma P st sigma :
  references P st -> map_ok P (fun _ => True) sigma -> references P (R.with_sigma st sigma).
Proof. intros H Hsigma; destruct H; constructor; cbn; auto. Qed.
Lemma references_queue P st queue :
  references P st -> Forall P queue -> references P (R.with_queue st queue).
Proof. intros H Hq; destruct H; constructor; cbn; auto. Qed.
Lemma references_readers P st readers :
  references P st -> map_ok P (set_ok P) readers -> references P (R.with_readers st readers).
Proof. intros H Hr; destruct H; constructor; cbn; auto. Qed.
Lemma references_contributions P st contributions :
  references P st -> map_ok P (map_ok P (fun _ => True)) contributions ->
  references P (R.with_contributions st contributions).
Proof. intros H Hc; destruct H; constructor; cbn; auto. Qed.
Lemma references_cells P st cells resets :
  references P st ->
  map_ok P (map_ok P (fun cell => option_ok P (R.side_reset_at cell))) cells ->
  map_ok P (Forall (pair_ok P)) resets -> references P (R.with_cells_and_resets st cells resets).
Proof. intros H Hc Hr; destruct H; constructor; cbn; auto. Qed.
Lemma references_targets P st targets :
  references P st -> map_ok P (set_ok P) targets -> references P (R.with_last_targets st targets).
Proof. intros H Ht; destruct H; constructor; cbn; auto. Qed.
Lemma references_controlled P st controlled :
  references P st -> set_ok P controlled -> references P (R.with_controlled st controlled).
Proof. intros H Hc; destruct H; constructor; cbn; auto. Qed.
Lemma references_observe P st x : references P st -> references P (R.observe st x).
Proof. unfold R.observe; destruct (Ranks.observe (R.ranking st) x); intro H; destruct H; constructor; cbn; auto. Qed.
Lemma lookup_set_ok P table x : map_ok P (set_ok P) table -> set_ok P (R.lookup_set table x).
Proof. intro H; unfold R.lookup_set; destruct (M.lookup table x) eqn:Hx; [exact (proj2 (H _ _ Hx)) |apply set_empty]. Qed.
Lemma references_materialize P st x : references P st -> P x -> references P (R.materialize st x).
Proof.
  intros H Hx; unfold R.materialize; destruct (M.lookup _ x); auto.
  apply references_sigma; auto; apply map_put; auto using refs_sigma.
Qed.
Lemma references_promote P st x : references P st -> P x -> references P (R.promote_controlled st x).
Proof. intros H Hx; apply references_controlled; auto; apply set_add; auto using refs_controlled. Qed.
Lemma references_enqueue P st x : references P st -> P x -> references P (R.enqueue st x).
Proof.
  intros H Hx; apply references_queue; auto; apply Forall_forall; intros y Hy;
    apply insert_members in Hy; destruct Hy as [->|Hy]; auto.
  eapply Forall_forall; [exact (refs_queue H) |exact Hy].
Qed.
Lemma references_enqueue_all P st xs : references P st -> Forall P xs -> references P (R.enqueue_all st xs).
Proof.
  intros H Hxs; pose proof (refs_queue H) as Hq; rewrite Forall_forall in Hxs, Hq.
  apply references_queue; auto; apply Forall_forall; intros y Hy;
    apply insert_all_members in Hy; destruct Hy; auto.
Qed.

Lemma set_weaken P Q values : (forall x, P x -> Q x) -> set_ok P values -> set_ok Q values.
Proof. firstorder. Qed.
Lemma option_weaken P Q value : (forall x, P x -> Q x) -> option_ok P value -> option_ok Q value.
Proof. destruct value; cbn; auto. Qed.
Lemma references_weaken P Q st :
  (forall x, P x -> Q x) -> references P st -> references Q st.
Proof.
  intros HP H; destruct H as [Hsig Hq Hr Hc Hcells Hresets Htargets Hcontrolled]; constructor.
  - eapply map_weaken; [exact HP |auto |exact Hsig].
  - eapply Forall_impl; eauto.
  - eapply map_weaken; [exact HP | |exact Hr].
    intros values Hvalues; eapply set_weaken; eauto.
  - eapply map_weaken; [exact HP | |exact Hc].
    intros row Hrow; eapply map_weaken; [exact HP |auto |exact Hrow].
  - eapply map_weaken; [exact HP | |exact Hcells].
    intros row Hrow; eapply map_weaken; [exact HP | |exact Hrow].
    intros cell Hcell; eapply option_weaken; eauto.
  - eapply map_weaken; [exact HP | |exact Hresets].
    intros ids Hids; eapply Forall_impl; [|exact Hids].
    intros [x y] [Hx Hy]; split; apply HP; assumption.
  - eapply map_weaken; [exact HP | |exact Htargets].
    intros values Hvalues; eapply set_weaken; eauto.
  - eapply set_weaken; eauto.
Qed.

Record frame_refs P fr := {
  ref_owner : P (R.frame_owner fr);
  ref_local : map_ok P (fun _ => True) (R.frame_local_side fr);
  ref_previous : set_ok P (R.frame_previous_targets fr);
  ref_current : set_ok P (R.frame_current_targets fr);
  ref_minimum : P (R.frame_min_scope fr);
  ref_maximum : option_ok P (R.frame_max_read fr)
}.
Lemma frame_weaken P Q fr :
  (forall x, P x -> Q x) -> frame_refs P fr -> frame_refs Q fr.
Proof.
  intros HP H; destruct H; constructor; eauto using map_weaken, set_weaken, option_weaken.
Qed.
Lemma frame_fresh P st owner phase : references P st -> P owner ->
  frame_refs P (R.fresh_frame st owner phase).
Proof.
  intros H Howner; constructor; cbn; auto using map_empty, set_empty.
  apply lookup_set_ok; exact (refs_targets H).
Qed.
Lemma frame_phase P fr phase : frame_refs P fr -> frame_refs P (R.with_frame_phase fr phase).
Proof. intro H; destruct H; constructor; cbn; auto. Qed.
Lemma frame_side P fr target input : frame_refs P fr -> P target ->
  frame_refs P (R.with_frame_side fr target input).
Proof. intros H Htarget; destruct H; constructor; cbn; auto using map_put, set_add. Qed.
Lemma frame_read P fr minimum maximum : frame_refs P fr -> P minimum -> option_ok P maximum ->
  frame_refs P (R.with_frame_read fr minimum maximum).
Proof. intros H Hmin Hmax; destruct H; constructor; cbn; auto. Qed.
Lemma reset_ids P table owner :
  map_ok P (Forall (pair_ok P)) table -> Forall (pair_ok P) (R.lookup_reset_ids table owner).
Proof.
  intro H; unfold R.lookup_reset_ids, R.side_cell_id; destruct (M.lookup table owner) eqn:Hlookup;
    [exact (proj2 (H _ _ Hlookup)) |constructor].
Qed.
Lemma removed_ids P id ids : Forall (pair_ok P) ids -> Forall (pair_ok P) (R.remove_cell_id id ids).
Proof.
  intro H; induction H; cbn; [constructor |destruct (R.cell_id_eq_dec id x); auto].
Qed.
Lemma added_id P id ids : pair_ok P id -> Forall (pair_ok P) ids ->
  Forall (pair_ok P) (R.add_cell_id id ids).
Proof. intros; unfold R.add_cell_id; destruct (in_dec R.cell_id_eq_dec id ids); auto. Qed.
Lemma stored_cell_refs P st source target : references P st ->
  option_ok P (R.side_reset_at (R.stored_side_cell st source target)).
Proof.
  intro H; unfold R.stored_side_cell; destruct (M.lookup _ target) eqn:Hlookup; [|exact I].
  exact (proj2 (@lookup_row _ P _ _ source (refs_cells H) _ _ Hlookup)).
Qed.
Lemma references_register P st source target scope phase :
  references P st -> P source -> P target -> P scope ->
  references P (R.register_reset st source target scope phase).
Proof.
  intros H Hsource Htarget Hscope.
  pose proof (stored_cell_refs source target H) as Hold.
  unfold R.register_reset.
  set (requested := if Features.restart_side_phases
    then if R.rank_lt st scope target then Some scope else None else None).
  assert (Hrequested : option_ok P requested) by
    (unfold requested; destruct Features.restart_side_phases, (R.rank_lt st scope target); cbn; auto).
  set (same := R.same_scope (R.side_reset_at (R.stored_side_cell st source target)) requested).
  set (without := if same then R.reset_at_close st else
    match R.side_reset_at (R.stored_side_cell st source target) with
    | Some previous => R.remove_registration (R.reset_at_close st) previous (source,target)
    | None => R.reset_at_close st end).
  assert (Hwithout : map_ok P (Forall (pair_ok P)) without).
  { unfold without; destruct same; [exact (refs_resets H) |].
    destruct (R.side_reset_at (R.stored_side_cell st source target)) as [previous|];
      [|exact (refs_resets H)].
    apply map_put; cbn in Hold; auto using refs_resets.
    apply removed_ids, reset_ids; exact (refs_resets H). }
  apply references_cells; [exact H |apply put_row; cbn; auto using refs_cells |].
  destruct same; [exact Hwithout |].
  destruct requested; [apply map_put; cbn in Hrequested; auto |exact Hwithout].
  apply added_id; [split; assumption |apply reset_ids; exact Hwithout].
Qed.
Lemma references_reset_cells P cells ids :
  map_ok P (map_ok P (fun cell => option_ok P (R.side_reset_at cell))) cells ->
  Forall (pair_ok P) ids ->
  map_ok P (map_ok P (fun cell => option_ok P (R.side_reset_at cell))) (R.reset_cells ids cells).
Proof.
  revert cells; induction ids as [|[source target] ids IH]; intros cells Hcells Hids; cbn; auto.
  inversion Hids as [|? ? Hpair Htail]; subst; destruct Hpair as [Hs Ht].
  apply IH; auto; apply put_row; cbn; auto.
Qed.
Lemma references_close P st owner : references P st -> P owner ->
  references P (R.reset_registered_cells st owner).
Proof.
  intros H Howner; unfold R.reset_registered_cells; destruct Features.restart_side_phases; auto.
  apply references_cells; auto.
  - apply references_reset_cells; auto using refs_cells; apply reset_ids; exact (refs_resets H).
  - apply map_put; auto using refs_resets; constructor.
Qed.
Lemma references_get P st fr target next next_fr value :
  references P st -> frame_refs P fr -> P target ->
  R.complete_get st fr target = (next,next_fr,value) ->
  references P next /\ frame_refs P next_fr.
Proof.
  intros Hst Hfr Htarget; unfold R.complete_get.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  assert (Hbase : references P base) by (unfold base; destruct (_ : bool); auto using references_promote).
  set (minimum := if R.rank_lt st target (R.frame_min_scope fr) then target else R.frame_min_scope fr).
  assert (Hmin : P minimum) by
    (unfold minimum; destruct (R.rank_lt st target (R.frame_min_scope fr));
      [exact Htarget |exact (ref_minimum Hfr)]).
  set (maximum := match R.frame_max_read fr with
    | None => Some target |Some previous => if R.rank_lt st previous target then Some target else Some previous end).
  assert (Hmax : option_ok P maximum).
  { unfold maximum; pose proof (ref_maximum Hfr) as Hprevious; unfold option_ok in *.
    destruct (R.frame_max_read fr) as [previous|]; cbn in *; [|exact Htarget].
    destruct (R.rank_lt st previous target); cbn; auto. }
  intro H; inversion H; subst next next_fr value; split.
  - apply references_materialize; auto.
    apply references_readers; [exact Hbase |].
    apply map_put; [exact (refs_readers Hbase) |exact Htarget |].
    apply set_add; [apply lookup_set_ok; exact (refs_readers Hbase) |exact (ref_owner Hfr)].
  - apply frame_read; auto.
Qed.
Lemma references_publish P st fr : references P st -> frame_refs P fr ->
  references P (R.publish_targets st fr).
Proof.
  intros Hst Hfr; apply references_targets; auto.
  apply map_put; [exact (refs_targets Hst) |exact (ref_owner Hfr) |exact (ref_current Hfr)].
Qed.
Lemma references_write P st fr target input next changed :
  references P st -> frame_refs P fr -> P target ->
  R.write_side_contribution st fr target input = (next,changed) -> references P next.
Proof.
  intros Hst Hfr Htarget; pose proof (ref_owner Hfr) as Howner;
    pose proof (ref_minimum Hfr) as Hmin; unfold R.write_side_contribution.
  set (base := R.promote_side_target st fr target).
  assert (Hbase : references P base) by
    (unfold base, R.promote_side_target; destruct (_ : bool); auto using references_promote).
  destruct (U.update _ _ _ _ _) as [phase value]; intro H; inversion H; subst next changed.
  apply references_register; eauto.
  apply references_contributions; auto; apply put_row; eauto using refs_contributions.
Qed.
Lemma references_commit P st fr direct next next_fr :
  references P st -> frame_refs P fr ->
  R.set_value st fr direct = (next,next_fr) -> references P next /\ frame_refs P next_fr.
Proof.
  intros Hst Hfr; pose proof (ref_owner Hfr) as Howner; unfold R.set_value.
  destruct (R.equivalent _ _) eqn:Hcandidate.
  - intro H; inversion H; subst; auto.
  - destruct (S.mem _ _) eqn:Hcontrolled;
      [destruct (U.update _ _ _ _ _) as [phase value] |]; cbn.
    all: match goal with |- context [if ?b then _ else _] => destruct b end;
      intro H; inversion H; subst next next_fr; split; auto using frame_phase.
    all: apply references_readers; [|apply map_put; auto using refs_readers, set_empty].
    all: apply references_enqueue_all;
      [apply references_sigma; auto; apply map_put; auto using refs_sigma
      |apply set_elements; apply lookup_set_ok; exact (refs_readers Hst)].
Qed.
Lemma references_requeue P before after owner : references P after -> P owner ->
  references P (R.requeue_changed_controlled_owner before after owner).
Proof.
  intros H Howner; apply references_queue; auto; apply Forall_forall; intros y Hy;
    apply requeue_members in Hy; destruct Hy as [->|Hy]; auto.
  eapply Forall_forall; [exact (refs_queue H) |exact Hy].
Qed.

Fixpoint stack_refs (P Code : V.t -> Prop) k : Prop :=
  match k with
  | R.KLoop => True
  | R.KSeedLoop roots => Forall Code roots
  | R.KAfterGet fr target next rest =>
      frame_refs P fr /\ P target /\
      (forall value, Sem.rhs_supported Code (next value)) /\ stack_refs P Code rest
  | R.KAfterSide fr next rest | R.KAfterSpawn fr next rest =>
      frame_refs P fr /\ Sem.rhs_supported Code next /\ stack_refs P Code rest
  | R.KDead fr _ pending rest =>
      frame_refs P fr /\ Forall P pending /\ stack_refs P Code rest
  | R.KDrain fr rest => frame_refs P fr /\ stack_refs P Code rest
  end.
Definition control_refs (P Code : V.t -> Prop) ctrl : Prop :=
  match ctrl with
  | R.RunLoop => True
  | R.RunSeeds roots |R.RunSeedLoop roots => Forall Code roots
  | R.StartEpisode owner k => P owner /\ stack_refs P Code k
  | R.RunRhs fr body k => frame_refs P fr /\ Sem.rhs_supported Code body /\ stack_refs P Code k
  | R.RunDead fr _ pending k => frame_refs P fr /\ Forall P pending /\ stack_refs P Code k
  | R.RunCommit fr _ k |R.RunDrain fr k => frame_refs P fr /\ stack_refs P Code k
  | R.Return k => stack_refs P Code k
  end.
Lemma stack_weaken P Q Code k : (forall x, P x -> Q x) -> stack_refs P Code k -> stack_refs Q Code k.
Proof.
  intros HP; induction k; cbn; intuition eauto using frame_weaken, Forall_impl.
Qed.
Lemma control_weaken P Q Code ctrl :
  (forall x, P x -> Q x) -> control_refs P Code ctrl -> control_refs Q Code ctrl.
Proof.
  intros HP; destruct ctrl; cbn; intuition eauto using frame_weaken, stack_weaken, Forall_impl.
Qed.
Lemma ordered_extend a b queue : extends a b -> Forall (ranked a) queue ->
  ordered a queue -> ordered b queue.
Proof.
  intros Hab Hr Hq; induction Hq as [|head tail Hq IH Hbelow]; constructor.
  - apply IH; inversion Hr; auto.
  - inversion Hr as [|? ? Hhead Htail]; subst.
    rewrite Forall_forall in Hbelow, Htail; apply Forall_forall; intros y Hin.
    rewrite (@lt_stable a b y head Hab (Htail _ Hin) Hhead); auto.
Qed.
Definition known (support : V.t -> Prop) st x := support x /\ ranked (R.ranking st) x.
Record store_wf support st := {
  store_valid : RL.valid (R.ranking st);
  store_references : references (known support st) st;
  store_ordered : ordered (R.ranking st) (R.queue st);
  store_distinct : NoDup (R.queue st)
}.
Lemma known_extend support st next : extends (R.ranking st) (R.ranking next) ->
  forall x, known support st x -> known support next x.
Proof. intros H x [Hx Hr]; split; auto; eapply extends_ranked; eauto. Qed.
Lemma known_ranked_queue support st : store_wf support st -> Forall (ranked (R.ranking st)) (R.queue st).
Proof.
  intro H; eapply Forall_impl with (P := known support st);
    [intros x [_ Hr]; exact Hr |exact (refs_queue (store_references H))].
Qed.
Lemma store_initial support : store_wf support R.empty_state.
Proof.
  constructor.
  - exact RL.empty_valid.
  - apply references_empty.
  - constructor.
  - constructor.
Qed.
Lemma store_observe support st target : store_wf support st -> support target ->
  store_wf support (R.observe st target) /\ known support (R.observe st target) target.
Proof.
  intros H Htarget; destruct (observe_order st target) as [Hext [Hrank Hvalid]].
  split; [constructor |split; auto].
  - exact (Hvalid (store_valid H)).
  - apply references_observe.
    eapply references_weaken; [apply known_extend; exact Hext |exact (store_references H)].
  - unfold R.observe in *; destruct (Ranks.observe (R.ranking st) target); cbn in *.
    eapply ordered_extend; eauto using known_ranked_queue, store_ordered.
  - unfold R.observe; destruct (Ranks.observe (R.ranking st) target); exact (store_distinct H).
Qed.
Lemma store_queue support st queue : store_wf support st ->
  Forall (known support st) queue -> ordered (R.ranking st) queue -> NoDup queue ->
  store_wf support (R.with_queue st queue).
Proof.
  intros H Hr Hq Hd; constructor.
  - exact (store_valid H).
  - apply references_queue; [exact (store_references H) |exact Hr].
  - exact Hq.
  - exact Hd.
Qed.
Lemma store_enqueue support st target : store_wf support st -> known support st target ->
  store_wf support (R.enqueue st target).
Proof.
  intros H Htarget; apply store_queue; auto.
  - apply Forall_forall; intros x Hin; apply insert_members in Hin; destruct Hin as [->|Hin]; auto.
    eapply Forall_forall; [exact (refs_queue (store_references H)) |exact Hin].
  - apply insert_ordered; eauto using store_valid, known_ranked_queue, store_ordered; exact (proj2 Htarget).
  - apply insert_distinct; exact (store_distinct H).
Qed.
Lemma insert_all_ordered order targets queue :
  RL.valid order -> Forall (ranked order) targets -> Forall (ranked order) queue ->
  ordered order queue -> ordered order (R.queue_insert_all order targets queue).
Proof.
  intros Hv Htargets; revert queue; induction Htargets as [|x xs Hx Hxs IH]; intros queue Hr Hq; cbn; auto.
  apply IH.
  - rewrite Forall_forall in Hr; apply Forall_forall; intros y Hy.
    apply insert_members in Hy; destruct Hy as [->|Hy]; auto.
  - apply insert_ordered; auto.
Qed.
Lemma store_enqueue_all support st targets : store_wf support st -> Forall (known support st) targets ->
  store_wf support (R.enqueue_all st targets).
Proof.
  intros H Htargets; apply store_queue; auto.
  - pose proof (refs_queue (store_references H)) as Hq;
      rewrite Forall_forall in Htargets, Hq.
    apply Forall_forall; intros x Hin; apply insert_all_members in Hin; destruct Hin; auto.
  - apply insert_all_ordered; [exact (store_valid H) | |exact (known_ranked_queue H) |exact (store_ordered H)].
    eapply Forall_impl with (P := known support st); [intros x [_ Hr]; exact Hr |exact Htargets].
  - apply insert_all_distinct; exact (store_distinct H).
Qed.

Lemma store_transfer support before after : store_wf support before ->
  R.ranking after = R.ranking before ->
  references (known support before) after ->
  ordered (R.ranking before) (R.queue after) -> NoDup (R.queue after) -> store_wf support after.
Proof.
  intros H Hrank Hrefs Hq Hd; constructor.
  - rewrite Hrank; exact (store_valid H).
  - eapply references_weaken; [|exact Hrefs].
    unfold known; rewrite Hrank; auto.
  - rewrite Hrank; exact Hq.
  - exact Hd.
Qed.
Lemma store_static support before after : store_wf support before ->
  R.ranking after = R.ranking before -> R.queue after = R.queue before ->
  references (known support before) after -> store_wf support after.
Proof.
  intros H Hr Hq Hrefs; eapply store_transfer; eauto;
    rewrite Hq; eauto using store_ordered, store_distinct.
Qed.
Lemma store_materialize support st owner : store_wf support st -> known support st owner ->
  store_wf support (R.materialize st owner).
Proof.
  intros H Howner; unfold R.materialize; destruct (M.lookup _ owner); auto.
  eapply store_static; [exact H |reflexivity |reflexivity |].
  apply references_sigma; [exact (store_references H) |apply map_put; auto using refs_sigma, store_references].
Qed.
Lemma get_layout st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  R.ranking next = R.ranking st /\ R.queue next = R.queue st /\
  R.contributions next = R.contributions st /\ R.side_cells next = R.side_cells st /\
  R.reset_at_close next = R.reset_at_close st /\ R.last_targets next = R.last_targets st /\
  R.frame_owner next_fr = R.frame_owner fr.
Proof.
  unfold R.complete_get, R.materialize, R.promote_controlled; intro H;
    split_program H; repeat split; reflexivity.
Qed.
Lemma store_get support st fr target next next_fr value :
  store_wf support st -> frame_refs (known support st) fr -> known support st target ->
  R.complete_get st fr target = (next,next_fr,value) ->
  store_wf support next /\ frame_refs (known support next) next_fr.
Proof.
  intros H Hfr Htarget Hget; destruct (get_layout Hget) as [Hr [Hq _]].
  destruct (references_get (store_references H) Hfr Htarget Hget) as [Hrefs Hnextfr]; split.
  - eapply store_static; eauto.
  - eapply frame_weaken; [|exact Hnextfr]; unfold known; rewrite Hr; auto.
Qed.
Lemma write_layout st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  R.ranking next = R.ranking st /\ R.queue next = R.queue st /\ R.sigma next = R.sigma st /\
  R.readers next = R.readers st /\ R.last_targets next = R.last_targets st.
Proof.
  unfold R.write_side_contribution, R.register_reset, R.promote_side_target, R.promote_controlled;
    intro H; split_program H; repeat split; reflexivity.
Qed.
Lemma store_write support st fr target input next changed :
  store_wf support st -> frame_refs (known support st) fr -> known support st target ->
  R.write_side_contribution st fr target input = (next,changed) -> store_wf support next.
Proof.
  intros H Hfr Htarget Hwrite; destruct (write_layout Hwrite) as [Hr [Hq _]].
  eapply store_static; eauto; eapply references_write; eauto using store_references.
Qed.
Lemma store_close support st owner : store_wf support st -> known support st owner ->
  store_wf support (R.reset_registered_cells st owner).
Proof.
  intros H Howner; eapply store_static; [exact H | | |apply references_close; auto using store_references].
  all: unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity.
Qed.
Lemma store_publish support st fr : store_wf support st -> frame_refs (known support st) fr ->
  store_wf support (R.publish_targets st fr).
Proof.
  intros H Hfr; eapply store_static; [exact H |reflexivity |reflexivity |].
  apply references_publish; auto using store_references.
Qed.
Lemma commit_queue st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  R.queue next = R.queue st \/ R.queue next =
    R.queue_insert_all (R.ranking st) (S.elements (R.lookup_set (R.readers st) (R.frame_owner fr))) (R.queue st).
Proof.
  unfold R.set_value; intro H; split_program H; cbn; auto.
Qed.
Lemma store_commit support st fr direct next next_fr :
  store_wf support st -> frame_refs (known support st) fr ->
  R.set_value st fr direct = (next,next_fr) ->
  store_wf support next /\ frame_refs (known support next) next_fr.
Proof.
  intros H Hfr Hset; pose proof
    (@commit_ranking st fr next next_fr (@commit_footprint st fr direct next next_fr Hset)) as Hr.
  destruct (@references_commit (known support st) st fr direct next next_fr (store_references H) Hfr Hset) as [Hrefs Hnextfr].
  assert (Hreaders : Forall (ranked (R.ranking st))
    (S.elements (R.lookup_set (R.readers st) (R.frame_owner fr)))).
  { eapply Forall_impl with (P := known support st); [intros x [_ Hx]; exact Hx |].
    apply set_elements, lookup_set_ok; exact (refs_readers (store_references H)). }
  split; [eapply store_transfer; eauto |].
  - destruct (@commit_queue st fr direct next next_fr Hset) as [Hq|Hq]; rewrite Hq; [exact (store_ordered H) |].
    apply insert_all_ordered;
      [exact (store_valid H) |exact Hreaders |exact (known_ranked_queue H) |exact (store_ordered H)].
  - destruct (@commit_queue st fr direct next next_fr Hset) as [Hq|Hq]; rewrite Hq;
      [exact (store_distinct H) |apply insert_all_distinct; exact (store_distinct H)].
  - eapply frame_weaken; [|exact Hnextfr]; unfold known; rewrite Hr; auto.
Qed.
Lemma store_requeue support before after owner : store_wf support after -> known support after owner ->
  store_wf support (R.requeue_changed_controlled_owner before after owner).
Proof.
  intros H Howner; unfold R.requeue_changed_controlled_owner; destruct (_ && _)%bool.
  - apply store_enqueue; auto.
  - destruct after; exact H.
Qed.

Lemma frame_rank_change support before after fr : R.ranking after = R.ranking before ->
  frame_refs (known support before) fr -> frame_refs (known support after) fr.
Proof. intros Hr Hfr; eapply frame_weaken; [|exact Hfr]; unfold known; rewrite Hr; auto. Qed.
Lemma stack_rank_change support before after k : R.ranking after = R.ranking before ->
  stack_refs (known support before) support k ->
  stack_refs (known support after) support k.
Proof. intros Hr Hk; eapply stack_weaken; [|exact Hk]; unfold known; rewrite Hr; auto. Qed.
Lemma materialize_rank st owner : R.ranking (R.materialize st owner) = R.ranking st.
Proof. unfold R.materialize; destruct (M.lookup _ owner); reflexivity. Qed.
Lemma close_rank st owner : R.ranking (R.reset_registered_cells st owner) = R.ranking st.
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity. Qed.
Definition config_wf support c := store_wf support (R.cfg_state c) /\
  control_refs (known support (R.cfg_state c)) support (R.cfg_control c).
Arguments store_observe {support st target} _ _.
Arguments store_get {support st fr target next next_fr value} _ _ _ _.
Arguments store_write {support st fr target input next changed} _ _ _ _.
Arguments get_layout {st fr target next next_fr value} _.
Arguments write_layout {st fr target input next changed} _.
Lemma continuation_side_wf support st fr target next k changed :
  store_wf support st -> frame_refs (known support st) fr -> known support st target ->
  Sem.rhs_supported support next ->
  stack_refs (known support st) support k ->
  config_wf support (R.continue_side st fr target next k changed).
Proof.
  intros Hst Hfr Htarget Hcode Hk; unfold R.continue_side;
    destruct changed; [destruct (_ && _)%bool |]; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs];
    auto using store_enqueue; tauto.
Qed.
Lemma continuation_dead_wf support st fr direct target pending k changed :
  store_wf support st -> frame_refs (known support st) fr -> known support st target ->
  Forall (known support st) pending -> stack_refs (known support st) support k ->
  config_wf support (R.continue_dead st fr direct target pending k changed).
Proof.
  intros Hst Hfr Htarget Hpending Hk; unfold R.continue_dead;
    destruct changed; [destruct (_ && _)%bool |]; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs];
    auto using store_enqueue; tauto.
Qed.
Lemma observed_context support st target fr k :
  store_wf support st -> support target ->
  frame_refs (known support st) fr -> stack_refs (known support st) support k ->
  store_wf support (R.observe st target) /\ known support (R.observe st target) target /\
  frame_refs (known support (R.observe st target)) fr /\
  stack_refs (known support (R.observe st target)) support k.
Proof.
  intros Hst Htarget Hfr Hk; destruct (store_observe Hst Htarget) as [Hnext Hknown].
  destruct (observe_order st target) as [Hext _].
  split; [exact Hnext |split; [exact Hknown |split]].
  - eapply frame_weaken; [apply known_extend; exact Hext |exact Hfr].
  - eapply stack_weaken; [apply known_extend; exact Hext |exact Hk].
Qed.
Arguments observed_context {support st target fr k} _ _ _ _.
Lemma store_pop support st owner rest : store_wf support st ->
  R.queue_pop (R.queue st) = Some (owner,rest) ->
  store_wf support (R.with_queue st rest) /\ known support st owner.
Proof.
  intros H Hpop; destruct (R.queue st) as [|head tail] eqn:Hqueue; cbn in Hpop; try discriminate.
  inversion Hpop; subst owner rest; pose proof (refs_queue (store_references H)) as Hr;
    rewrite Hqueue in Hr; inversion Hr; subst.
  split; [apply store_queue; auto |assumption].
  - pose proof (store_ordered H) as Hq; rewrite Hqueue in Hq; inversion Hq; auto.
  - pose proof (store_distinct H) as Hd; rewrite Hqueue in Hd; inversion Hd; auto.
Qed.
Arguments store_pop {support st owner rest} _ _.
Lemma code_child_supported Code body : Sem.rhs_supported Code body ->
  match body with
  | R.ConstraintSystem.Ret _ => True
  | R.ConstraintSystem.Get target next => Code target /\ forall value, Sem.rhs_supported Code (next value)
  | R.ConstraintSystem.Side target _ next |R.ConstraintSystem.Spawn target next =>
      Code target /\ Sem.rhs_supported Code next
  end.
Proof. intro H; destruct H; cbn; auto. Qed.
Arguments code_child_supported {Code body} _.
Lemma next_configuration_wf support tf before after :
  (forall owner, support owner -> Sem.rhs_supported support (tf owner)) ->
  config_wf support before -> step tf before after -> config_wf support after.
Proof.
  intros Htf; destruct before as [st ctrl]; intros [Hst Hctrl] Hstep;
    unfold step, R.next_config in Hstep; cbn in Hctrl.
  cbn [R.cfg_state] in Hst.
  destruct ctrl as [|roots|roots|owner k|fr body k|fr direct pending k|fr direct k|fr k|k].
  all: cbn [R.cfg_state R.cfg_control] in Hstep; cbn [control_refs] in Hctrl.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|] eqn:Hpop; try discriminate.
    inversion Hstep; subst after; destruct (store_pop Hst Hpop) as [Hnext Howner].
    split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; auto.
  - destruct roots as [|root roots].
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; auto.
    + inversion Hctrl as [|? ? Hroot Hroots]; subst.
      destruct (store_observe Hst Hroot) as [Hnext Hknown].
      destruct (R.is_materialized (R.observe st root)); inversion Hstep; subst after;
        split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; auto.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|] eqn:Hpop.
    + inversion Hstep; subst after; destruct (store_pop Hst Hpop) as [Hnext Howner].
      split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; auto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; auto.
  - destruct Hctrl as [Howner Hk]; inversion Hstep; subst after.
    pose proof (store_materialize Hst Howner) as Hmat.
    assert (HownerMat : known support (R.materialize st owner) owner) by
      (unfold known; rewrite materialize_rank; exact Howner).
    split; [exact Hmat |]; cbn [R.cfg_state R.cfg_control control_refs stack_refs].
    split; [apply frame_fresh; [exact (store_references Hmat) |exact HownerMat] |].
    split; [apply Htf; exact (proj1 Howner) |eapply stack_rank_change; [apply materialize_rank |exact Hk]].
  - destruct Hctrl as [Hfr [Hbody Hk]]; pose proof (code_child_supported Hbody) as Hcode;
      destruct body as [direct|target next|target raw next|target next]; cbn in Hcode.
    + inversion Hstep; subst after; split; [exact Hst |]; cbn [R.cfg_state R.cfg_control control_refs stack_refs].
      split; [exact Hfr |split; [|exact Hk]].
      destruct Features.eliminate_dead_sides; [apply set_elements; exact (ref_previous Hfr) |constructor].
    + destruct Hcode as [Htarget Hcode].
      destruct (observed_context Hst Htarget Hfr Hk) as [Hobs [Hknown [Hfr0 Hk0]]].
      set (st0 := R.observe st target) in *.
      destruct (negb (R.is_materialized st0 target) && R.rank_lt st0 (R.frame_owner fr) target)%bool.
      * inversion Hstep; subst after; split; [exact Hobs |]; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
      * set (st1 := if R.is_materialized st0 target then st0 else R.enqueue st0 target) in *.
        assert (Hst1 : store_wf support st1) by (unfold st1; destruct (_ : bool); auto using store_enqueue).
        assert (Hr1 : R.ranking st1 = R.ranking st0) by (unfold st1; destruct (_ : bool); reflexivity).
        assert (Hfr1 : frame_refs (known support st1) fr) by (eapply frame_rank_change; eauto).
        assert (Htarget1 : known support st1 target) by (unfold known in *; rewrite Hr1; exact Hknown).
        destruct (R.complete_get st1 fr target) as [[done next_fr] value] eqn:Hget.
        inversion Hstep; subst after; destruct (store_get Hst1 Hfr1 Htarget1 Hget) as [Hdone Hnextfr].
        destruct (get_layout Hget) as [Hr _].
        split; [exact Hdone |]; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; split; [exact Hnextfr |].
        split; [apply Hcode |eapply stack_rank_change; [rewrite Hr; exact Hr1 |exact Hk0]].
    + destruct Hcode as [Htarget Hcode].
      destruct (observed_context Hst Htarget Hfr Hk) as [Hobs [Hknown [Hfr0 Hk0]]].
      unfold R.record_side_input in Hstep.
      set (fr1 := R.with_frame_side fr target (R.accumulated_side_input fr target raw)) in *.
      assert (Hfr1 : frame_refs (known support (R.observe st target)) fr1) by (apply frame_side; auto).
      destruct (R.write_side_contribution (R.observe st target) fr1 target
        (R.accumulated_side_input fr target raw)) as [done changed] eqn:Hwrite.
      inversion Hstep; subst after; pose proof (store_write Hobs Hfr1 Hknown Hwrite) as Hdone.
      destruct (write_layout Hwrite) as [Hr _].
      apply continuation_side_wf; auto.
      * eapply frame_rank_change; eauto.
      * unfold known; rewrite Hr; exact Hknown.
      * eapply stack_rank_change; eauto.
    + destruct Hcode as [Htarget Hcode].
      destruct (observed_context Hst Htarget Hfr Hk) as [Hobs [Hknown [Hfr0 Hk0]]].
      destruct (R.is_materialized (R.observe st target)).
      * inversion Hstep; subst after; split; [exact Hobs |];
          cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
      * destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target).
        -- inversion Hstep; subst after; split; [exact Hobs |];
             cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
        -- inversion Hstep; subst after; split.
           ++ apply store_materialize; [apply store_enqueue; auto |exact Hknown].
           ++ cbn [R.cfg_state R.cfg_control control_refs stack_refs]; split.
              ** eapply frame_rank_change; [apply materialize_rank |exact Hfr0].
              ** split; [exact Hcode |eapply stack_rank_change; [apply materialize_rank |exact Hk0]].
  - destruct Hctrl as [Hfr [Hpending Hk]]; destruct pending as [|target pending].
    + inversion Hstep; subst after; split; [apply store_publish; auto |]; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
    + inversion Hpending as [|? ? Htarget Htail]; subst.
      destruct (S.mem target (R.frame_current_targets fr)).
      * inversion Hstep; subst after; split; [exact Hst |]; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
      * destruct (R.write_side_contribution st fr target D.bottom) as [done changed] eqn:Hwrite.
        inversion Hstep; subst after; pose proof (store_write Hst Hfr Htarget Hwrite) as Hdone.
        destruct (write_layout Hwrite) as [Hr _]; apply continuation_dead_wf; auto.
        -- eapply frame_rank_change; eauto.
        -- unfold known; rewrite Hr; exact Htarget.
        -- eapply Forall_impl with (P := known support st); [unfold known; rewrite Hr; auto |exact Htail].
        -- eapply stack_rank_change; eauto.
  - destruct Hctrl as [Hfr Hk]; destruct (R.set_value st fr direct) as [done next_fr] eqn:Hset.
    inversion Hstep; subst after; destruct (@store_commit support st fr direct done next_fr Hst Hfr Hset) as [Hdone Hnextfr].
    pose proof (@commit_ranking st fr done next_fr (@commit_footprint st fr direct done next_fr Hset)) as Hr.
    split; [apply store_requeue; [exact Hdone |unfold known; rewrite Hr; exact (ref_owner Hfr)] |].
    cbn [R.cfg_state R.cfg_control control_refs stack_refs]; split; [exact Hnextfr |eapply stack_rank_change; eauto].
  - destruct Hctrl as [Hfr Hk]; destruct (R.queue_peek (R.queue st)) as [next|] eqn:Hpeek.
    + destruct (V.eq_dec next (R.frame_owner fr)) as [Heq|Hneq].
      * destruct (R.queue_pop (R.queue st)) as [[head rest]|] eqn:Hpop; try discriminate.
        inversion Hstep; subst after; destruct (store_pop Hst Hpop) as [Hnext _].
        split; [exact Hnext |]; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; split.
        -- apply frame_fresh; auto using store_references; exact (ref_owner Hfr).
        -- split; [apply Htf; exact (proj1 (ref_owner Hfr)) |exact Hk].
      * destruct (R.rank_lt st (R.frame_owner fr) next).
        -- destruct (R.queue_pop (R.queue st)) as [[head rest]|] eqn:Hpop; try discriminate.
           assert (Hhead : head = next) by (destruct (R.queue st); cbn in *; congruence).
           subst head; inversion Hstep; subst after; destruct (store_pop Hst Hpop) as [Hnext Htarget].
           split; [exact Hnext |]; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
        -- inversion Hstep; subst after; split; [apply store_close; auto; exact (ref_owner Hfr) |].
           cbn [R.cfg_state R.cfg_control control_refs]; eapply stack_rank_change; [apply close_rank |exact Hk].
    + inversion Hstep; subst after; split; [apply store_close; auto; exact (ref_owner Hfr) |].
           cbn [R.cfg_state R.cfg_control control_refs]; eapply stack_rank_change; [apply close_rank |exact Hk].
  - destruct k as [|roots|fr target next k|fr next k|fr next k|fr direct pending k|fr k]; cbn in Hctrl.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; auto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; auto.
    + destruct Hctrl as [Hfr [Htarget [Hcode Hk]]].
      destruct (R.complete_get st fr target) as [[done next_fr] value] eqn:Hget.
      inversion Hstep; subst after; destruct (store_get Hst Hfr Htarget Hget) as [Hdone Hnextfr].
      destruct (get_layout Hget) as [Hr _]; split; [exact Hdone |]; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; split; auto.
      split; [apply Hcode |eapply stack_rank_change; eauto].
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs]; tauto.
Qed.
Theorem reachable_configuration_wf tf roots (finite : Sem.finite_system tf roots) c :
  steps tf (R.initial_config roots) c -> config_wf (fun x => In x (Sem.support finite)) c.
Proof.
  intro Hpath; assert (Hinitial : config_wf (fun x => In x (Sem.support finite)) (R.initial_config roots)).
  { split; [apply store_initial |].
    cbn [R.cfg_state R.cfg_control control_refs stack_refs]; apply Forall_forall; apply Sem.initial_supported. }
  revert Hinitial; induction Hpath; auto; intro Hfirst; apply IHHpath.
  eapply next_configuration_wf; eauto using Sem.system_supported.
Qed.

Lemma code_unrestricted body : Sem.rhs_supported (fun _ => True) body.
Proof. induction body; constructor; auto. Qed.
Theorem reachable_rank_configuration tf roots c : steps tf (R.initial_config roots) c -> config_wf (fun _ => True) c.
Proof.
  intro Hpath; assert (Hinitial : config_wf (fun _ => True) (R.initial_config roots)).
  { split; [apply store_initial |apply Forall_forall; auto]. }
  revert Hinitial; induction Hpath; auto; intro Hfirst; apply IHHpath.
  eapply next_configuration_wf; [intros owner _; apply code_unrestricted |exact Hfirst |exact H].
Qed.

(** A logical predicate on residual code replaces a history of all earlier
    observations in the upper-bound proof. Only bounded reads may be supplied
    to a continuation. *)
Inductive bounded_rhs (upper : V.t -> D.t) (owner : V.t) : Syntax.rhs -> Prop :=
| BoundedRet direct : D.leq direct (upper owner) = true ->
    bounded_rhs upper owner (Syntax.Ret direct)
| BoundedGet target next :
    (forall value, D.leq value (upper target) = true -> bounded_rhs upper owner (next value)) ->
    bounded_rhs upper owner (Syntax.Get target next)
| BoundedSide target raw next : D.leq raw (upper target) = true ->
    bounded_rhs upper owner next -> bounded_rhs upper owner (Syntax.Side target raw next)
| BoundedSpawn target next : bounded_rhs upper owner next ->
    bounded_rhs upper owner (Syntax.Spawn target next).

Lemma observation_total values body : exists result, Sem.observes_at values body result.
Proof.
  induction body as [direct |target next IH |target raw next IH |target next IH].
  - eexists; split; [constructor |intros x value Hin; contradiction].
  - destruct (IH (values target)) as [result [Hobs Hreads]].
    eexists; split; [econstructor; exact Hobs |].
    intros x value [Heq |Hin]; [inversion Heq; reflexivity |exact (Hreads x value Hin)].
  - destruct IH as [result [Hobs Hreads]].
    eexists; split; [econstructor; exact Hobs |exact Hreads].
  - destruct IH as [result [Hobs Hreads]].
    eexists; split; [econstructor; exact Hobs |exact Hreads].
Qed.

Definition bounded_observations upper owner body :=
  forall result, Sem.rhs_observes body result ->
  Sem.Observation.prefix_reads_below upper (Sem.observed_reads result) ->
  D.leq (Sem.observed_direct result) (upper owner) = true /\
  Sem.valuation_side_effects_below upper (Sem.observed_sides result).

Lemma bounded_observations_code upper owner body :
  bounded_observations upper owner body -> bounded_rhs upper owner body.
Proof.
  induction body as [direct |target next IH |target raw next IH |target next IH]; intro H.
  - apply BoundedRet.
    assert (Hr : Sem.Observation.prefix_reads_below upper []) by (intros x value Hin; contradiction).
    exact (proj1 (H _ (Sem.ObserveRet direct) Hr)).
  - constructor; intros value Hvalue; apply IH.
    intros result Hobs Hreads.
    apply (H _ (@Sem.ObserveGet target value next result Hobs)).
    intros x observed [Heq |Hin]; [inversion Heq; subst; exact Hvalue |eauto].
  - constructor.
    + destruct (observation_total upper next) as [result [Hobs Hreads]].
      assert (Hbelow : Sem.Observation.prefix_reads_below upper (Sem.observed_reads result)).
      { intros x value Hin; rewrite (Hreads x value Hin); apply DL.leq_refl. }
      exact (proj2 (H _ (@Sem.ObserveSide target raw next result Hobs) Hbelow) target raw (or_introl eq_refl)).
    + apply IH; intros result Hobs Hreads.
      destruct (H _ (@Sem.ObserveSide target raw next result Hobs) Hreads) as [Hdirect Hsides].
      split; [exact Hdirect |intros x value Hin; apply Hsides; right; exact Hin].
  - constructor; apply IH; intros result Hobs Hreads.
    exact (H _ (@Sem.ObserveSpawn target next result Hobs) Hreads).
Qed.

Lemma monotone_code_bounded tf support upper owner :
  Sem.system_monotone_on tf support -> Sem.post_solution_on tf support upper ->
  In owner support -> bounded_rhs upper owner (tf owner).
Proof.
  intros Hmono Hupper Howner; apply bounded_observations_code.
  intros lower Hlower Hreads.
  destruct (observation_total upper (tf owner)) as [higher [Hhigher Hhigher_reads]].
  assert (Hcommon : Sem.common_read_values_le lower higher).
  { intros target low high Hlow Hhigh; rewrite (Hhigher_reads target high Hhigh); eauto. }
  pose proof (@Sem.system_dependencies_monotone tf support Hmono owner Howner lower higher Hlower Hhigher Hcommon) as Hdeps.
  assert (Hvalues : Sem.valued_events_le (Sem.observed_reads lower) (Sem.observed_reads higher)).
  { intros target value Hin.
    assert (Htarget : In target (map fst (Sem.observed_reads lower))) by (apply in_map_iff; exists (target,value); split; [reflexivity |exact Hin]).
    destruct (in_map_iff fst (Sem.observed_reads higher) target) as [Hback _].
    destruct (Hback (Hdeps target Htarget)) as [[x high] [Heq Hhigh]]; cbn in Heq; subst x.
    exists high; split; auto; eapply Hcommon; eauto. }
  pose proof (@Sem.system_effects_monotone tf support Hmono owner Howner lower higher Hlower Hhigher Hvalues) as Heffects.
  destruct (Hupper owner Howner higher (conj Hhigher Hhigher_reads)) as [Hdirect [Hsides _]].
  split.
  - eapply DL.leq_trans; [exact (Sem.Observation.direct_effect_le Heffects) |exact Hdirect].
  - intros target value Hin.
    destruct (Sem.Observation.side_effects_le Heffects target value Hin) as [high [Hhigh Hle]].
    eapply DL.leq_trans; [exact Hle |apply Hsides; exact Hhigh].
Qed.

Record bounded_state (upper : V.t -> D.t) st := {
  bounded_sigma : forall x, D.leq (R.sigma_value st x) (upper x) = true;
  bounded_aggregate : forall x, D.leq (R.aggregate st x) (upper x) = true
}.
Definition bounded_frame upper fr := forall target value,
  M.lookup (R.frame_local_side fr) target = Some value -> D.leq value (upper target) = true.
Fixpoint bounded_stack upper k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => True
  | R.KAfterGet fr target next rest => bounded_frame upper fr /\
      (forall value, D.leq value (upper target) = true -> bounded_rhs upper (R.frame_owner fr) (next value)) /\
      bounded_stack upper rest
  | R.KAfterSide fr next rest | R.KAfterSpawn fr next rest => bounded_frame upper fr /\
      bounded_rhs upper (R.frame_owner fr) next /\ bounded_stack upper rest
  | R.KDead fr direct _ rest => bounded_frame upper fr /\
      D.leq direct (upper (R.frame_owner fr)) = true /\ bounded_stack upper rest
  | R.KDrain fr rest => bounded_frame upper fr /\ bounded_stack upper rest
  end.
Definition bounded_control upper ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
  | R.StartEpisode _ k | R.Return k => bounded_stack upper k
  | R.RunRhs fr body k => bounded_frame upper fr /\
      bounded_rhs upper (R.frame_owner fr) body /\ bounded_stack upper k
  | R.RunDead fr direct _ k | R.RunCommit fr direct k => bounded_frame upper fr /\
      D.leq direct (upper (R.frame_owner fr)) = true /\ bounded_stack upper k
  | R.RunDrain fr k => bounded_frame upper fr /\ bounded_stack upper k
  end.
Definition bounded_config upper c := bounded_state upper (R.cfg_state c) /\
  bounded_control upper (R.cfg_control c).

Lemma bound_empty upper : bounded_state upper R.empty_state.
Proof.
  constructor; intro x; unfold R.sigma_value, R.aggregate, R.lookup_map; cbn;
    rewrite ML.lookup_empty; auto using DL.bottom_least.
  rewrite ML.values_empty; apply DL.bottom_least.
Qed.
Lemma bound_layout upper st next : R.sigma next = R.sigma st ->
  R.contributions next = R.contributions st -> bounded_state upper st -> bounded_state upper next.
Proof. intros Hs Hc [Hs0 Hc0]; constructor; unfold R.sigma_value, R.aggregate; now rewrite ?Hs, ?Hc. Qed.
Lemma bound_sigma_update upper st x value : bounded_state upper st ->
  D.leq value (upper x) = true -> bounded_state upper (R.with_sigma st (M.update (R.sigma st) x value)).
Proof.
  intros H Hvalue; constructor; [|exact (bounded_aggregate H)].
  intro y; unfold R.sigma_value; cbn; destruct (V.eq_dec y x) as [-> |Hneq].
  - rewrite ML.lookup_update_same; exact Hvalue.
  - rewrite ML.lookup_update_other; auto; exact (bounded_sigma H y).
Qed.
Lemma bound_materialize upper st x : bounded_state upper st -> bounded_state upper (R.materialize st x).
Proof.
  intro H; unfold R.materialize; destruct (M.lookup (R.sigma st) x); auto.
  apply bound_sigma_update; auto using DL.bottom_least.
Qed.
Lemma bound_observe upper st x : bounded_state upper st -> bounded_state upper (R.observe st x).
Proof. unfold R.observe; destruct (Ranks.observe _ _); apply bound_layout; reflexivity. Qed.
Lemma bound_queue upper st q : bounded_state upper st -> bounded_state upper (R.with_queue st q).
Proof. apply bound_layout; reflexivity. Qed.
Lemma bound_enqueue upper st x : bounded_state upper st -> bounded_state upper (R.enqueue st x).
Proof. apply bound_queue. Qed.
Lemma bound_close upper st x : bounded_state upper st -> bounded_state upper (R.reset_registered_cells st x).
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; apply bound_layout; reflexivity. Qed.
Lemma bound_publish upper st fr : bounded_state upper st -> bounded_state upper (R.publish_targets st fr).
Proof. apply bound_layout; reflexivity. Qed.
Lemma bound_frame_fresh upper st owner phase : bounded_frame upper (R.fresh_frame st owner phase).
Proof. intros target value H; cbn in H; rewrite ML.lookup_empty in H; discriminate. Qed.
Lemma bound_frame_read upper fr minimum maximum : bounded_frame upper fr ->
  bounded_frame upper (R.with_frame_read fr minimum maximum).
Proof. exact (fun H => H). Qed.
Lemma bound_frame_phase upper fr phase : bounded_frame upper fr -> bounded_frame upper (R.with_frame_phase fr phase).
Proof. exact (fun H => H). Qed.
Lemma bound_frame_side upper fr target value : bounded_frame upper fr -> D.leq value (upper target) = true ->
  bounded_frame upper (R.with_frame_side fr target value).
Proof.
  intros H Hvalue x v Hlookup; cbn in Hlookup; destruct (V.eq_dec x target) as [-> |Hneq].
  - rewrite ML.lookup_update_same in Hlookup; inversion Hlookup; subst; exact Hvalue.
  - rewrite ML.lookup_update_other in Hlookup; eauto.
Qed.
Lemma bound_accumulated upper fr target raw : bounded_frame upper fr -> D.leq raw (upper target) = true ->
  D.leq (R.accumulated_side_input fr target raw) (upper target) = true.
Proof.
  intros H Hraw; unfold R.accumulated_side_input.
  destruct (M.lookup (R.frame_local_side fr) target) eqn:Hlookup; auto; apply DL.join_least; eauto.
Qed.
Lemma bound_get upper st fr target next next_fr value : bounded_state upper st -> bounded_frame upper fr ->
  R.complete_get st fr target = (next,next_fr,value) ->
  bounded_state upper next /\ bounded_frame upper next_fr /\ D.leq value (upper target) = true /\
  R.frame_owner next_fr = R.frame_owner fr.
Proof.
  intros Hst Hfr; unfold R.complete_get; intro H.
  set (st0 := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) in *.
  set (st1 := R.with_readers st0
    (M.update (R.readers st0) target (S.add (R.frame_owner fr) (R.lookup_set (R.readers st0) target)))) in *.
  assert (H0 : bounded_state upper st0).
  { unfold st0; destruct (R.rank_lt _ _ _); auto; eapply bound_layout with (st := st); [reflexivity |reflexivity |exact Hst]. }
  assert (H1 : bounded_state upper (R.materialize st1 target)).
  { apply bound_materialize; eapply bound_layout with (st := st0); [reflexivity |reflexivity |exact H0]. }
  inversion H; subst next next_fr value; split; [exact H1 |].
  split; [apply bound_frame_read; exact Hfr |split; [exact (bounded_sigma H1 target) |reflexivity]].
Qed.
Lemma folded_update_bound row x value upper : D.leq (R.join_values (M.values row)) upper = true ->
  D.leq value upper = true -> D.leq (R.join_values (M.values (M.update row x value))) upper = true.
Proof.
  intros Hrow Hvalue; destruct (ML.values_update row x value) as [rest [Hnext Hold]].
  apply fold_bound; intros v Hin; apply (Permutation_in v Hnext) in Hin; cbn in Hin.
  destruct Hin as [-> |Hin]; auto.
  apply DL.leq_trans with (y := R.join_values (M.values row)); [apply folded_member |exact Hrow].
  destruct (M.lookup row x); apply (Permutation_in v (Permutation_sym Hold)); cbn; auto.
Qed.
Lemma bound_contribution upper st source target value : bounded_state upper st ->
  D.leq value (upper target) = true -> bounded_state upper
    (R.with_contributions st (R.update_map (R.contributions st) target source value)).
Proof.
  intros H Hvalue; constructor; [exact (bounded_sigma H) |].
  intro x; unfold R.aggregate; cbn; destruct (V.eq_dec x target) as [-> |Hneq].
  - unfold R.update_map, R.lookup_map; rewrite ML.lookup_update_same.
    apply folded_update_bound; [exact (bounded_aggregate H target) |exact Hvalue].
  - rewrite row_other; auto; exact (bounded_aggregate H x).
Qed.

Lemma bound_register upper st source target scope phase : bounded_state upper st ->
  bounded_state upper (R.register_reset st source target scope phase).
Proof. intro H; eapply bound_layout with (st := st); [reflexivity |reflexivity |exact H]. Qed.

Section UpperBounds.
Variable update_bounded : forall side x phase old input upper,
  D.leq old upper = true -> D.leq input upper = true ->
  D.leq (snd (U.update side x phase old input)) upper = true.

Lemma bound_write upper st fr target input next changed : bounded_state upper st ->
  D.leq input (upper target) = true -> R.write_side_contribution st fr target input = (next,changed) ->
  bounded_state upper next.
Proof.
  intros Hst Hinput; unfold R.write_side_contribution; intro H.
  set (st0 := R.promote_side_target st fr target) in *.
  assert (H0 : bounded_state upper st0).
  { unfold st0, R.promote_side_target; destruct (R.rank_lt _ _ _); auto;
      eapply bound_layout with (st := st); [reflexivity |reflexivity |exact Hst]. }
  inversion H; subst next changed; apply bound_register; apply bound_contribution; [exact H0 |].
  apply update_bounded; [|exact Hinput].
  eapply DL.leq_trans; [apply contribution_below_aggregate |exact (bounded_aggregate H0 target)].
Qed.
Lemma bound_commit upper st fr direct next next_fr : bounded_state upper st ->
  D.leq direct (upper (R.frame_owner fr)) = true -> R.set_value st fr direct = (next,next_fr) ->
  bounded_state upper next /\ (bounded_frame upper fr -> bounded_frame upper next_fr).
Proof.
  intros Hst Hdirect; unfold R.set_value; intro H.
  destruct (R.equivalent _ _) eqn:Hcandidate; [inversion H; subst next next_fr; auto |].
  assert (Hinput : D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (upper (R.frame_owner fr)) = true)
    by (apply DL.join_least; auto using bounded_aggregate).
  destruct (S.mem (R.frame_owner fr) (R.controlled st)).
  - destruct (U.update _ _ _ _ _) as [phase value] eqn:Hupdate; cbn in H.
    assert (Hvalue : D.leq value (upper (R.frame_owner fr)) = true).
    { pose proof (@update_bounded false (R.frame_owner fr) (R.frame_phase fr)
        (R.sigma_value st (R.frame_owner fr)) _ _ (bounded_sigma Hst _) Hinput) as Hb.
      rewrite Hupdate in Hb; exact Hb. }
    destruct (R.equivalent value (R.sigma_value st (R.frame_owner fr))); inversion H; subst next next_fr; split;
      auto using bound_frame_phase;
      eapply bound_layout with (st := R.with_sigma st (M.update (R.sigma st) (R.frame_owner fr) _));
      [reflexivity |reflexivity |apply bound_sigma_update; auto].
  - cbn in H; rewrite Hcandidate in H; inversion H; subst next next_fr; split;
      auto using bound_frame_phase;
      eapply bound_layout with (st := R.with_sigma st (M.update (R.sigma st) (R.frame_owner fr) _));
      [reflexivity |reflexivity |apply bound_sigma_update; auto].
Qed.

Lemma bounded_ret upper owner direct : bounded_rhs upper owner (Syntax.Ret direct) ->
  D.leq direct (upper owner) = true.
Proof. intro H; inversion H; assumption. Qed.
Lemma bounded_get upper owner target next : bounded_rhs upper owner (Syntax.Get target next) ->
  forall value, D.leq value (upper target) = true -> bounded_rhs upper owner (next value).
Proof. intro H; inversion H; assumption. Qed.
Lemma bounded_side upper owner target raw next : bounded_rhs upper owner (Syntax.Side target raw next) ->
  D.leq raw (upper target) = true /\ bounded_rhs upper owner next.
Proof. intro H; inversion H; auto. Qed.
Lemma bounded_spawn upper owner target next : bounded_rhs upper owner (Syntax.Spawn target next) ->
  bounded_rhs upper owner next.
Proof. intro H; inversion H; assumption. Qed.
Lemma bound_requeue upper before after owner : bounded_state upper after ->
  bounded_state upper (R.requeue_changed_controlled_owner before after owner).
Proof. apply bound_queue. Qed.
Lemma bound_continue_side upper st fr target next k changed : bounded_state upper st -> bounded_frame upper fr ->
  bounded_rhs upper (R.frame_owner fr) next -> bounded_stack upper k ->
  bounded_config upper (R.continue_side st fr target next k changed).
Proof.
  intros; unfold R.continue_side; destruct changed; [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))%bool |];
    split; cbn [R.cfg_state R.cfg_control bounded_control bounded_stack]; intuition auto using bound_enqueue.
Qed.
Lemma bound_continue_dead upper st fr direct target pending k changed : bounded_state upper st -> bounded_frame upper fr ->
  D.leq direct (upper (R.frame_owner fr)) = true -> bounded_stack upper k ->
  bounded_config upper (R.continue_dead st fr direct target pending k changed).
Proof.
  intros; unfold R.continue_dead; destruct changed; [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))%bool |];
    split; cbn [R.cfg_state R.cfg_control bounded_control bounded_stack]; intuition auto using bound_enqueue.
Qed.

Arguments bound_get {upper st fr target next next_fr value} _ _ _.
Arguments bound_write {upper st fr target input next changed} _ _ _.
Arguments bound_commit {upper st fr direct next next_fr} _ _ _.

Theorem next_configuration_bounded tf support upper before after :
  (forall owner, In owner support -> bounded_rhs upper owner (tf owner)) ->
  config_wf (fun x => In x support) before -> bounded_config upper before -> step tf before after -> bounded_config upper after.
Proof.
  intros Htf [Hwf Hrefs] [Hst Hctrl] Hstep.
  destruct before as [st ctrl]; destruct ctrl as
    [|roots|roots|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control control_refs bounded_control] in Hwf, Hrefs, Hst, Hctrl |- *.
  all: cbn [R.cfg_state R.cfg_control] in Hstep.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; try discriminate.
    inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control bounded_control bounded_stack]; auto using bound_queue.
  - destruct roots as [|root roots].
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control bounded_control]; auto.
    + destruct (R.is_materialized (R.observe st root)); inversion Hstep; subst after;
        split; cbn [R.cfg_state R.cfg_control bounded_control bounded_stack]; auto using bound_observe.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; inversion Hstep; subst after;
      split; cbn [R.cfg_state R.cfg_control bounded_control bounded_stack]; auto using bound_queue.
  - destruct Hrefs as [Howner Hk]; inversion Hstep; subst after; split.
    + apply bound_materialize; exact Hst.
    + cbn [R.cfg_state R.cfg_control bounded_control]; split; [apply bound_frame_fresh |].
      split; [apply Htf; exact (proj1 Howner) |exact Hctrl].
  - destruct Hctrl as [Hfr [Hcode Hk]]; destruct body as [direct |target next |target raw next |target next].
    + inversion Hstep; subst after; split; [exact Hst |].
      cbn [R.cfg_state R.cfg_control bounded_control]; split; [exact Hfr |split; [eapply bounded_ret; exact Hcode |exact Hk]].
    + pose proof (@bounded_get upper (R.frame_owner fr) target next Hcode) as Hnext.
      destruct (negb (R.is_materialized (R.observe st target) target) &&
        R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
      * inversion Hstep; subst after; split; [apply bound_observe; exact Hst |].
        cbn [R.cfg_state R.cfg_control bounded_control bounded_stack]; tauto.
      * set (st0 := if R.is_materialized (R.observe st target) target then R.observe st target
          else R.enqueue (R.observe st target) target) in *.
        assert (H0 : bounded_state upper st0) by
          (unfold st0; destruct (R.is_materialized (R.observe st target) target); auto using bound_observe, bound_enqueue).
        destruct (R.complete_get st0 fr target) as [[done next_fr] value] eqn:Hget.
        destruct (bound_get H0 Hfr Hget) as [Hdone [Hfr1 [Hvalue Howner]]].
        inversion Hstep; subst after; split; [exact Hdone |].
        cbn [R.cfg_state R.cfg_control bounded_control]; split; [exact Hfr1 |split; [rewrite Howner; apply Hnext; exact Hvalue |exact Hk]].
    + destruct (@bounded_side upper (R.frame_owner fr) target raw next Hcode) as [Hraw Hnext].
      unfold R.record_side_input in Hstep.
      set (input := R.accumulated_side_input fr target raw) in *.
      assert (Hinput : D.leq input (upper target) = true) by (apply bound_accumulated; auto).
      destruct (R.write_side_contribution (R.observe st target) (R.with_frame_side fr target input) target input)
        as [done changed] eqn:Hwrite.
      pose proof (bound_write (bound_observe target Hst) Hinput Hwrite) as Hdone.
      inversion Hstep; subst after; apply bound_continue_side; auto using bound_frame_side.
    + pose proof (@bounded_spawn upper (R.frame_owner fr) target next Hcode) as Hnext.
      destruct (R.is_materialized (R.observe st target) target); [|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target)];
        inversion Hstep; subst after; split;
        cbn [R.cfg_state R.cfg_control bounded_control bounded_stack];
        auto using bound_observe, bound_enqueue, bound_materialize.
  - destruct Hctrl as [Hfr [Hdirect Hk]]; destruct pending as [|target pending].
    + inversion Hstep; subst after; split; [apply bound_publish; exact Hst |];
        cbn [R.cfg_state R.cfg_control bounded_control]; tauto.
    + destruct (S.mem target (R.frame_current_targets fr)).
      * inversion Hstep; subst after; split; [exact Hst |]; cbn [R.cfg_state R.cfg_control bounded_control]; tauto.
      * destruct (R.write_side_contribution st fr target D.bottom) as [done changed] eqn:Hwrite.
        pose proof (bound_write Hst (DL.bottom_least (upper target)) Hwrite) as Hdone.
        inversion Hstep; subst after; apply bound_continue_dead; auto.
  - destruct Hctrl as [Hfr [Hdirect Hk]].
    destruct (R.set_value st fr direct) as [done next_fr] eqn:Hset.
    destruct (bound_commit Hst Hdirect Hset) as [Hdone Hfr1].
    pose proof (@commit_owner st fr done next_fr (@commit_footprint st fr direct done next_fr Hset)) as Howner.
    inversion Hstep; subst after; split; [apply bound_requeue; exact Hdone |];
      cbn [R.cfg_state R.cfg_control bounded_control]; auto.
  - destruct Hctrl as [Hfr Hk]; destruct Hrefs as [Hfr_refs Hk_refs].
    destruct (R.queue_peek (R.queue st)) as [next|].
    + destruct (V.eq_dec next (R.frame_owner fr)).
      * destruct (R.queue_pop (R.queue st)) as [[head rest]|]; try discriminate.
        inversion Hstep; subst after; split; [apply bound_queue; exact Hst |].
        cbn [R.cfg_state R.cfg_control bounded_control]; split; [apply bound_frame_fresh |].
        split; [apply Htf; exact (proj1 (ref_owner Hfr_refs)) |exact Hk].
      * destruct (R.rank_lt st (R.frame_owner fr) next).
        -- destruct (R.queue_pop (R.queue st)) as [[head rest]|]; try discriminate.
           inversion Hstep; subst after; split; [apply bound_queue; exact Hst |].
           cbn [R.cfg_state R.cfg_control bounded_control bounded_stack]; tauto.
        -- inversion Hstep; subst after; split; [apply bound_close; exact Hst |]; cbn [R.cfg_state R.cfg_control bounded_control]; exact Hk.
    + inversion Hstep; subst after; split; [apply bound_close; exact Hst |]; cbn [R.cfg_state R.cfg_control bounded_control]; exact Hk.
  - destruct k as [|roots|fr target next k|fr next k|fr next k|fr direct pending k|fr k]; cbn in Hctrl.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control bounded_control]; auto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control bounded_control]; auto.
    + destruct Hctrl as [Hfr [Hnext Hk]].
      destruct (R.complete_get st fr target) as [[done next_fr] value] eqn:Hget.
      destruct (bound_get Hst Hfr Hget) as [Hdone [Hfr1 [Hvalue Howner]]].
      inversion Hstep; subst after; split; [exact Hdone |]; cbn [R.cfg_state R.cfg_control bounded_control];
        split; [exact Hfr1 |split; [rewrite Howner; apply Hnext; exact Hvalue |exact Hk]].
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control bounded_control]; auto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control bounded_control]; auto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control bounded_control]; auto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control bounded_control]; auto.
Qed.

Theorem reachable_configuration_bounded tf roots (finite : Sem.finite_system tf roots) upper c :
  Sem.system_monotone_on tf (Sem.support finite) -> Sem.post_solution_on tf (Sem.support finite) upper ->
  steps tf (R.initial_config roots) c -> bounded_config upper c.
Proof.
  intros Hmono Hupper Hpath.
  assert (Hcodes : forall owner, In owner (Sem.support finite) -> bounded_rhs upper owner (tf owner))
    by (intros; eapply monotone_code_bounded; eauto).
  assert (Hinitial : bounded_config upper (R.initial_config roots)) by (split; [apply bound_empty |exact I]).
  assert (Hwf : config_wf (fun x => In x (Sem.support finite)) (R.initial_config roots)) by (eapply reachable_configuration_wf; constructor).
  revert Hwf Hinitial; induction Hpath; auto; intros Hwf Hfirst; apply IHHpath.
  - eapply next_configuration_wf; eauto using Sem.system_supported.
  - eapply next_configuration_bounded; eauto.
Qed.
Theorem successful_run_below fuel tf roots (finite : Sem.finite_system tf roots) final upper :
  Sem.system_monotone_on tf (Sem.support finite) -> Sem.post_solution_on tf (Sem.support finite) upper ->
  R.solve_fuel fuel tf roots = Some final ->
  forall x, D.leq (R.sigma_value final x) (upper x) = true.
Proof.
  intros Hmono Hupper Hrun; destruct (@successful_path fuel tf roots final Hrun) as [Hpath Hquiet].
  destruct (@reachable_configuration_bounded tf roots finite upper (terminal final) Hmono Hupper Hpath) as [Hfinal _].
  exact (bounded_sigma Hfinal).
Qed.
End UpperBounds.

(** One deterministic observation, once all reads are fixed. This also bridges
    the structural semantics (which records spawns) and partial-store replay. *)
Lemma observation_unique values body left right : Sem.observes_at values body left ->
  Sem.observes_at values body right -> left = right.
Proof.
  intros [Hleft Hl] [Hright Hr]; revert right Hright Hr;
    induction Hleft; intros other Hother Hreads; inversion Hother; subst.
  - reflexivity.
  - assert (Heq : value = value0).
    { rewrite (Hl target value (or_introl eq_refl)), (Hreads target value0 (or_introl eq_refl)); reflexivity. }
    subst value0; assert (Heq : result = result0).
    { apply IHHleft; auto; intros x v Hin; [apply Hl |apply Hreads]; right; exact Hin. }
    now rewrite Heq.
  - assert (Heq : result = result0) by (apply IHHleft; auto); now rewrite Heq.
  - assert (Heq : result = result0) by (apply IHHleft; auto); now rewrite Heq.
Qed.
Lemma observation_replay st body result : Sem.rhs_observes body result ->
  (forall target value, In (target,value) (Sem.observed_reads result) -> M.lookup (R.sigma st) target = Some value) ->
  replay st body (Sem.observed_direct result) (Sem.observed_reads result) (Sem.observed_sides result).
Proof.
  intros Hobs; induction Hobs; intro Hreads; cbn.
  - constructor.
  - econstructor; [apply Hreads; left; reflexivity |apply IHHobs; intros; apply Hreads; right; assumption].
  - constructor; apply IHHobs; exact Hreads.
  - constructor; apply IHHobs; exact Hreads.
Qed.
Lemma replay_observation st body direct reads effects : replay st body direct reads effects ->
  exists result, Sem.observes_at (R.sigma_value st) body result /\
    Sem.observed_direct result = direct /\ Sem.observed_reads result = reads /\ Sem.observed_sides result = effects.
Proof.
  intro H; induction H as [direct |target value next direct reads effects Hlookup Htail [result [[Hobs Hreads] [Hd [Hr He]]]]
    |target value next direct reads effects Htail [result [[Hobs Hreads] [Hd [Hr He]]]]
    |target next direct reads effects Htail [result [[Hobs Hreads] [Hd [Hr He]]]]].
  - eexists; split; [split; [constructor |intros x value Hin; contradiction] |repeat split; reflexivity].
  - eexists; split; [split; [econstructor; exact Hobs |] |cbn; repeat split; congruence].
    intros x v [Heq |Hin]; [inversion Heq; subst x v; unfold R.sigma_value; change (M.lookup (R.sigma st) target = Some value) in Hlookup; now rewrite Hlookup |apply Hreads; exact Hin].
  - eexists; split; [split; [econstructor; exact Hobs |exact Hreads] |cbn; repeat split; congruence].
  - eexists; split; [split; [econstructor; exact Hobs |exact Hreads] |cbn; repeat split; congruence].
Qed.
Lemma read_value st target value : M.lookup (R.sigma st) target = Some value -> R.sigma_value st target = value.
Proof. unfold R.sigma_value; intro H; now rewrite H. Qed.

Definition observation_prefix (body residual : Syntax.rhs)
  (reads sides : list (V.t * D.t)) (spawns : list V.t) :=
  forall result, Sem.rhs_observes residual result -> Sem.rhs_observes body
    {| Sem.Observation.observed_direct := Sem.observed_direct result;
       Sem.Observation.observed_reads := reads ++ Sem.observed_reads result;
       Sem.Observation.observed_sides := sides ++ Sem.observed_sides result;
       Sem.Observation.observed_spawns := spawns ++ Sem.observed_spawns result |}.
Lemma prefix_fresh body : observation_prefix body body [] [] [].
Proof. intros [direct reads sides spawns] H; exact H. Qed.
Lemma prefix_get origin target next reads sides spawns value :
  observation_prefix origin (Syntax.Get target next) reads sides spawns ->
  observation_prefix origin (next value) (reads ++ [(target,value)]) sides spawns.
Proof.
  intros H result Hobs; pose proof (H _ (@Sem.ObserveGet target value next result Hobs)) as Hp.
  cbn in Hp; unfold observation_prefix; intros; rewrite <- app_assoc; exact Hp.
Qed.
Lemma prefix_side origin target value next reads sides spawns :
  observation_prefix origin (Syntax.Side target value next) reads sides spawns ->
  observation_prefix origin next reads (sides ++ [(target,value)]) spawns.
Proof.
  intros H result Hobs; pose proof (H _ (@Sem.ObserveSide target value next result Hobs)) as Hp.
  cbn in Hp; rewrite <- app_assoc; exact Hp.
Qed.
Lemma prefix_spawn origin target next reads sides spawns :
  observation_prefix origin (Syntax.Spawn target next) reads sides spawns ->
  observation_prefix origin next reads sides (spawns ++ [target]).
Proof.
  intros H result Hobs; pose proof (H _ (@Sem.ObserveSpawn target next result Hobs)) as Hp.
  cbn in Hp; rewrite <- app_assoc; exact Hp.
Qed.
Lemma prefix_return origin direct reads sides spawns :
  observation_prefix origin (Syntax.Ret direct) reads sides spawns -> Sem.rhs_observes origin
    {| Sem.Observation.observed_direct := direct;
       Sem.Observation.observed_reads := reads;
       Sem.Observation.observed_sides := sides;
       Sem.Observation.observed_spawns := spawns |}.
Proof.
  intro H; pose proof (H _ (Sem.ObserveRet direct)) as Hp; cbn in Hp;
    repeat rewrite app_nil_r in Hp; exact Hp.
Qed.

Definition watched_reads st owner reads := forall target value, In (target,value) reads ->
  M.lookup (R.sigma st) target = Some value /\ S.mem owner (R.lookup_set (R.readers st) target) = true.
Record completed_observation tf st owner := {
  completed_result : Sem.observation;
  completed_trace : Sem.rhs_observes (tf owner) completed_result;
  completed_reads : watched_reads st owner (Sem.observed_reads completed_result);
  completed_direct : D.leq (Sem.observed_direct completed_result) (R.sigma_value st owner) = true;
  completed_sides : forall target raw, In (target,raw) (Sem.observed_sides completed_result) ->
    D.leq raw (R.stored_contribution st owner target) = true;
  completed_spawns : forall target, In target (Sem.observed_spawns completed_result) -> solved st target
}.
Lemma completed_is_post_solution tf st owner (done : completed_observation tf st owner) :
  (forall target raw, In (target,raw) (Sem.observed_sides (completed_result done)) ->
    D.leq (R.aggregate st target) (R.sigma_value st target) = true) -> owner_post_solution tf st owner.
Proof.
  intro Haggregate; destruct done as [result Htrace Hreads Hdirect Hsides Hspawns].
  assert (Hlookup : forall target value, In (target,value) (Sem.observed_reads result) -> M.lookup (R.sigma st) target = Some value)
    by (intros; exact (proj1 (Hreads _ _ H))).
  assert (Hat : Sem.observes_at (R.sigma_value st) (tf owner) result).
  { split; [exact Htrace |intros target value Hin; symmetry; apply read_value; apply Hlookup; exact Hin]. }
  split.
  - exists (Sem.observed_direct result), (Sem.observed_reads result), (Sem.observed_sides result).
    apply observation_replay; auto.
  - split.
    + intros direct reads sides Hreplay.
      destruct (replay_observation Hreplay) as [other [Hother [Hd [Hr Hs]]]].
      assert (Heq : result = other) by (eapply observation_unique; eauto); subst other.
      rewrite <- Hd, <- Hs; split; [exact Hdirect |intros target raw Hin].
      eapply DL.leq_trans; [apply Hsides; exact Hin |].
      eapply DL.leq_trans; [apply contribution_below_aggregate |apply (Haggregate target raw); exact Hin].
    + intros other Hother target Hin.
      assert (Heq : result = other) by (eapply observation_unique; eauto); subst other.
      apply Hspawns; exact Hin.
Qed.
(** Structural purity includes every possible continuation of a read. Spawns
    remain ordinary operations. *)
Inductive pure_rhs : Syntax.rhs -> Prop :=
| PureRet value : pure_rhs (Syntax.Ret value)
| PureGet target next : (forall value, pure_rhs (next value)) -> pure_rhs (Syntax.Get target next)
| PureSpawn target next : pure_rhs next -> pure_rhs (Syntax.Spawn target next).
Lemma pure_observations body :
  (forall result, Sem.rhs_observes body result -> Sem.observed_sides result = []) -> pure_rhs body.
Proof.
  induction body as [value |target next IH |target raw next IH |target next IH]; intro H.
  - constructor.
  - constructor; intro value; apply IH; intros result Hobs.
    exact (H _ (@Sem.ObserveGet target value next result Hobs)).
  - destruct (observation_total (fun _ => D.bottom) next) as [result [Hobs _]].
    discriminate (H _ (@Sem.ObserveSide target raw next result Hobs)).
  - constructor; apply IH; intros result Hobs; exact (H _ (@Sem.ObserveSpawn target next result Hobs)).
Qed.
Lemma pure_get target next : pure_rhs (Syntax.Get target next) -> forall value, pure_rhs (next value).
Proof. intro H; inversion H; assumption. Qed.
Lemma pure_spawn target next : pure_rhs (Syntax.Spawn target next) -> pure_rhs next.
Proof. intro H; inversion H; assumption. Qed.
Lemma pure_no_side target raw next : pure_rhs (Syntax.Side target raw next) -> False.
Proof. intro H; inversion H. Qed.
Lemma pure_sides body result : pure_rhs body -> Sem.rhs_observes body result -> Sem.observed_sides result = [].
Proof.
  intros Hpure Hobs; revert Hpure; induction Hobs; intro Hpure; inversion Hpure; subst; cbn; auto.
Qed.
Record ordinary_store st := {
  ordinary_contributions : R.contributions st = M.empty R.contribution_row;
  ordinary_targets : forall owner, S.elements (R.lookup_set (R.last_targets st) owner) = []
}.
Record ordinary_frame fr := {
  ordinary_local : R.frame_local_side fr = M.empty D.t;
  ordinary_previous : S.elements (R.frame_previous_targets fr) = [];
  ordinary_current : S.elements (R.frame_current_targets fr) = []
}.
Fixpoint ordinary_stack k : Prop :=
  match k with
  | R.KLoop |R.KSeedLoop _ => True
  | R.KAfterGet fr _ next rest => ordinary_frame fr /\ (forall value, pure_rhs (next value)) /\ ordinary_stack rest
  | R.KAfterSpawn fr next rest => ordinary_frame fr /\ pure_rhs next /\ ordinary_stack rest
  | R.KDrain fr rest => ordinary_frame fr /\ ordinary_stack rest
  | R.KAfterSide _ _ _ |R.KDead _ _ _ _ => False
  end.
Definition ordinary_control ctrl :=
  match ctrl with
  | R.RunLoop |R.RunSeeds _ |R.RunSeedLoop _ => True
  | R.StartEpisode _ k |R.Return k => ordinary_stack k
  | R.RunRhs fr body k => ordinary_frame fr /\ pure_rhs body /\ ordinary_stack k
  | R.RunDead fr _ pending k => ordinary_frame fr /\ pending = [] /\ ordinary_stack k
  | R.RunCommit fr _ k |R.RunDrain fr k => ordinary_frame fr /\ ordinary_stack k
  end.
Definition ordinary_config c := ordinary_store (R.cfg_state c) /\ ordinary_control (R.cfg_control c).
Lemma set_elements_empty : S.elements S.empty = [].
Proof.
  destruct (S.elements S.empty) as [|x xs] eqn:H; auto.
  assert (Hm : S.mem x S.empty = true) by (apply SL.mem_spec; rewrite H; left; reflexivity).
  rewrite SL.empty_spec in Hm; discriminate.
Qed.
Lemma ordinary_initial : ordinary_store R.empty_state.
Proof. constructor; [reflexivity |intro x; unfold R.lookup_set; cbn; rewrite ML.lookup_empty; apply set_elements_empty]. Qed.
Lemma ordinary_layout st next : R.contributions next = R.contributions st -> R.last_targets next = R.last_targets st ->
  ordinary_store st -> ordinary_store next.
Proof. intros Hc Ht [Hc0 Ht0]; constructor; [now rewrite Hc |unfold R.lookup_set; now rewrite Ht]. Qed.
Lemma ordinary_materialize st x : ordinary_store st -> ordinary_store (R.materialize st x).
Proof.
  intro H; unfold R.materialize; destruct (M.lookup (R.sigma st) x); auto;
    eapply ordinary_layout with (st := st); [reflexivity |reflexivity |exact H].
Qed.
Lemma ordinary_observe st x : ordinary_store st -> ordinary_store (R.observe st x).
Proof. intro H; unfold R.observe; destruct (Ranks.observe _ _); eapply ordinary_layout with (st := st); eauto. Qed.
Lemma ordinary_queue st q : ordinary_store st -> ordinary_store (R.with_queue st q).
Proof. intro H; eapply ordinary_layout with (st := st); eauto. Qed.
Lemma ordinary_enqueue st x : ordinary_store st -> ordinary_store (R.enqueue st x).
Proof. apply ordinary_queue. Qed.
Lemma ordinary_close st x : ordinary_store st -> ordinary_store (R.reset_registered_cells st x).
Proof. intro H; unfold R.reset_registered_cells; destruct Features.restart_side_phases; eapply ordinary_layout with (st := st); eauto. Qed.
Lemma ordinary_requeue before after x : ordinary_store after -> ordinary_store (R.requeue_changed_controlled_owner before after x).
Proof. apply ordinary_queue. Qed.
Lemma ordinary_fresh st x phase : ordinary_store st -> ordinary_frame (R.fresh_frame st x phase).
Proof. intro H; constructor; cbn; auto using ordinary_targets, set_elements_empty. Qed.
Lemma ordinary_read fr minimum maximum : ordinary_frame fr -> ordinary_frame (R.with_frame_read fr minimum maximum).
Proof. intros [Hl Hp Hc]; constructor; assumption. Qed.
Lemma ordinary_phase fr phase : ordinary_frame fr -> ordinary_frame (R.with_frame_phase fr phase).
Proof. intros [Hl Hp Hc]; constructor; assumption. Qed.
Lemma ordinary_get st fr target next next_fr value : ordinary_store st -> ordinary_frame fr ->
  R.complete_get st fr target = (next,next_fr,value) -> ordinary_store next /\ ordinary_frame next_fr.
Proof.
  intros Hst Hfr; unfold R.complete_get; intro H; destruct (R.rank_lt st (R.frame_owner fr) target);
    inversion H; subst next next_fr value; split; auto using ordinary_read;
    apply ordinary_materialize; eapply ordinary_layout with (st := st); eauto.
Qed.
Lemma ordinary_publish st fr : ordinary_store st -> ordinary_frame fr -> ordinary_store (R.publish_targets st fr).
Proof.
  intros Hst Hfr; constructor; [exact (ordinary_contributions Hst) |].
  intro x; unfold R.publish_targets, R.lookup_set; cbn; destruct (V.eq_dec x (R.frame_owner fr)) as [-> |Hneq].
  - rewrite ML.lookup_update_same; exact (ordinary_current Hfr).
  - rewrite ML.lookup_update_other; auto; exact (ordinary_targets Hst x).
Qed.
Lemma ordinary_commit st fr direct next next_fr : ordinary_store st -> ordinary_frame fr ->
  R.set_value st fr direct = (next,next_fr) -> ordinary_store next /\ ordinary_frame next_fr.
Proof.
  intros Hst Hfr Hset; pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview; split.
  - eapply ordinary_layout with (st := st); eauto using commit_contributions, commit_targets.
  - unfold R.set_value in Hset; split_program Hset; auto using ordinary_phase.
Qed.
Arguments ordinary_get {st fr target next next_fr value} _ _ _.
Arguments ordinary_commit {st fr direct next next_fr} _ _ _.
Theorem ordinary_step tf before after : (forall owner, pure_rhs (tf owner)) ->
  ordinary_config before -> step tf before after -> ordinary_config after.
Proof.
  intros Htf; destruct before as [st ctrl]; intros [Hst Hctrl] Hstep;
    unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control ordinary_control] in Hst, Hctrl.
  destruct ctrl as [|roots|roots|owner k|fr body k|fr direct pending k|fr direct k|fr k|k].
  all: cbn [R.cfg_state R.cfg_control] in Hstep; cbn [ordinary_control] in Hctrl.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; try discriminate.
    inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control ordinary_control ordinary_stack]; auto using ordinary_queue.
  - destruct roots as [|root roots].
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control ordinary_control]; auto.
    + destruct (R.is_materialized (R.observe st root)); inversion Hstep; subst after;
        split; cbn [R.cfg_state R.cfg_control ordinary_control ordinary_stack]; auto using ordinary_observe.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; inversion Hstep; subst after;
      split; cbn [R.cfg_state R.cfg_control ordinary_control ordinary_stack]; auto using ordinary_queue.
  - inversion Hstep; subst after; pose proof (ordinary_materialize owner Hst) as Hmat.
    split; [exact Hmat |]; cbn [R.cfg_state R.cfg_control ordinary_control]; auto using ordinary_fresh.
  - destruct Hctrl as [Hfr [Hcode Hk]]; destruct body as [direct |target next |target raw next |target next].
    + inversion Hstep; subst after; split; [exact Hst |]; cbn [R.cfg_state R.cfg_control ordinary_control].
      rewrite (ordinary_previous Hfr); destruct Features.eliminate_dead_sides; auto.
    + pose proof (pure_get Hcode) as Hnext.
      destruct (negb (R.is_materialized (R.observe st target) target) && R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
      * inversion Hstep; subst after; split; [apply ordinary_observe; exact Hst |]; cbn [R.cfg_state R.cfg_control ordinary_control ordinary_stack]; auto.
      * set (st0 := if R.is_materialized (R.observe st target) target then R.observe st target else R.enqueue (R.observe st target) target) in *.
        assert (H0 : ordinary_store st0) by (unfold st0; destruct (R.is_materialized (R.observe st target) target); auto using ordinary_observe, ordinary_enqueue).
        destruct (R.complete_get st0 fr target) as [[done next_fr] value] eqn:Hget.
        inversion Hstep; subst after; destruct (ordinary_get H0 Hfr Hget) as [Hdone Hfr1].
        split; [exact Hdone |]; cbn [R.cfg_state R.cfg_control ordinary_control]; auto.
    + exfalso; eapply pure_no_side; exact Hcode.
    + pose proof (pure_spawn Hcode) as Hnext.
      destruct (R.is_materialized (R.observe st target) target); [|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target)];
        inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control ordinary_control ordinary_stack];
        intuition auto using ordinary_observe, ordinary_enqueue, ordinary_materialize.
  - destruct Hctrl as [Hfr [-> Hk]]; inversion Hstep; subst after; split; [apply ordinary_publish; auto |];
      cbn [R.cfg_state R.cfg_control ordinary_control]; auto.
  - destruct Hctrl as [Hfr Hk]; destruct (R.set_value st fr direct) as [done next_fr] eqn:Hset.
    inversion Hstep; subst after; destruct (ordinary_commit Hst Hfr Hset) as [Hdone Hfr1].
    split; [apply ordinary_requeue; exact Hdone |]; cbn [R.cfg_state R.cfg_control ordinary_control]; auto.
  - destruct Hctrl as [Hfr Hk]; destruct (R.queue_peek (R.queue st)) as [next|].
    + destruct (V.eq_dec next (R.frame_owner fr)).
      * destruct (R.queue_pop (R.queue st)) as [[head rest]|]; try discriminate.
        inversion Hstep; subst after; split; [apply ordinary_queue; exact Hst |];
          cbn [R.cfg_state R.cfg_control ordinary_control]; auto using ordinary_fresh, ordinary_queue.
      * destruct (R.rank_lt st (R.frame_owner fr) next).
        -- destruct (R.queue_pop (R.queue st)) as [[head rest]|]; try discriminate.
           inversion Hstep; subst after; split; [apply ordinary_queue; exact Hst |]; cbn [R.cfg_state R.cfg_control ordinary_control ordinary_stack]; auto.
        -- inversion Hstep; subst after; split; [apply ordinary_close; exact Hst |]; cbn [R.cfg_state R.cfg_control ordinary_control]; exact Hk.
    + inversion Hstep; subst after; split; [apply ordinary_close; exact Hst |]; cbn [R.cfg_state R.cfg_control ordinary_control]; exact Hk.
  - destruct k as [|roots|fr target next k|fr next k|fr next k|fr direct pending k|fr k]; cbn in Hctrl; try contradiction.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control ordinary_control]; auto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control ordinary_control]; auto.
    + destruct Hctrl as [Hfr [Hnext Hk]]; destruct (R.complete_get st fr target) as [[done next_fr] value] eqn:Hget.
      inversion Hstep; subst after; destruct (ordinary_get Hst Hfr Hget) as [Hdone Hfr1].
      split; [exact Hdone |]; cbn [R.cfg_state R.cfg_control ordinary_control]; auto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control ordinary_control]; auto.
    + inversion Hstep; subst after; split; cbn [R.cfg_state R.cfg_control ordinary_control]; auto.
Qed.
Theorem ordinary_reachable tf roots c : no_side_effects tf -> steps tf (R.initial_config roots) c -> ordinary_config c.
Proof.
  intros Hpure Hpath; assert (Hcode : forall owner, pure_rhs (tf owner)) by (intro; apply pure_observations; apply Hpure).
  assert (Hinitial : ordinary_config (R.initial_config roots)) by (split; [apply ordinary_initial |exact I]).
  revert Hinitial; induction Hpath; auto; intro Hfirst; apply IHHpath; eapply ordinary_step; eauto.
Qed.
Corollary ordinary_aggregate tf roots c target : no_side_effects tf -> steps tf (R.initial_config roots) c ->
  R.aggregate (R.cfg_state c) target = D.bottom.
Proof.
  intros Hpure Hpath; destruct (@ordinary_reachable tf roots c Hpure Hpath) as [Hst _].
  unfold R.aggregate, R.lookup_map; rewrite (ordinary_contributions Hst), ML.lookup_empty, ML.values_empty; reflexivity.
Qed.
Lemma get_rank st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) -> R.ranking next = R.ranking st.
Proof. intro H; exact (proj1 (get_layout H)). Qed.
Lemma get_owner st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) -> R.frame_owner next_fr = R.frame_owner fr.
Proof. intro H; destruct (get_layout H) as [_ [_ [_ [_ [_ [_ Howner]]]]]]; exact Howner. Qed.
Lemma write_rank st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) -> R.ranking next = R.ranking st.
Proof. intro H; exact (proj1 (write_layout H)). Qed.
Lemma observe_extends st target : extends (R.ranking st) (R.ranking (R.observe st target)).
Proof. exact (proj1 (observe_order st target)). Qed.
Ltac primitive_ranks :=
  repeat match goal with
  | H : R.complete_get _ _ _ = (_,_,_) |- _ =>
      let Hr := fresh "get_ranking" in pose proof (get_rank H) as Hr; clear H
  | H : R.write_side_contribution _ _ _ _ = (_,_) |- _ =>
      let Hr := fresh "write_ranking" in pose proof (write_rank H) as Hr; clear H
  | H : R.set_value ?st ?fr ?direct = (?next,?next_fr) |- _ =>
      let Hr := fresh "commit_ranking" in pose proof (@commit_ranking st fr next next_fr (@commit_footprint st fr direct next next_fr H)) as Hr; clear H
  end.
Lemma next_ranking_extends tf before after : step tf before after ->
  extends (R.ranking (R.cfg_state before)) (R.ranking (R.cfg_state after)).
Proof.
  destruct before as [st ctrl]; unfold step, R.next_config; intro H;
    cbn [R.cfg_state R.cfg_control] in H |- *.
  destruct ctrl; cbn [R.cfg_control] in H;
    unfold R.continue_side, R.continue_dead in H; split_program H;
    primitive_ranks;
    cbn [R.cfg_state R.ranking R.with_queue R.enqueue R.enqueue_all
      R.requeue_changed_controlled_owner R.publish_targets];
    repeat rewrite materialize_rank; repeat rewrite close_rank;
    repeat match goal with Hr : R.ranking _ = R.ranking _ |- _ => rewrite Hr; clear Hr end;
    cbn [R.enqueue R.with_queue R.ranking]; auto using extends_refl, observe_extends.
  all: repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [R.enqueue R.with_queue R.ranking]; auto using extends_refl, observe_extends.
Qed.

Fixpoint suspended_owners k : list V.t :=
  match k with
  | R.KLoop | R.KSeedLoop _ => []
  | R.KAfterGet fr _ _ rest |R.KAfterSide fr _ rest |R.KAfterSpawn fr _ rest
  | R.KDead fr _ _ rest |R.KDrain fr rest => R.frame_owner fr :: suspended_owners rest
  end.
Definition active_owners ctrl : list V.t :=
  match ctrl with
  | R.RunLoop |R.RunSeeds _ |R.RunSeedLoop _ => []
  | R.StartEpisode owner k => owner :: suspended_owners k
  | R.RunRhs fr _ k |R.RunDead fr _ _ k |R.RunCommit fr _ k |R.RunDrain fr k => R.frame_owner fr :: suspended_owners k
  | R.Return k => suspended_owners k
  end.
Lemma suspended_references P Code k : stack_refs P Code k -> Forall P (suspended_owners k).
Proof.
  induction k; cbn [stack_refs suspended_owners]; intro H; auto using Forall.
  all: destruct H as [Hfr Hrest]; constructor; [exact (ref_owner Hfr) |apply IHk; tauto].
Qed.
Lemma active_references P Code ctrl : control_refs P Code ctrl -> Forall P (active_owners ctrl).
Proof.
  destruct ctrl; cbn [control_refs active_owners]; intro H; try solve [constructor |eapply (@suspended_references P Code); exact H].
  all: destruct H as [Howner Hrest]; constructor; [try exact Howner; exact (ref_owner Howner) |eapply (@suspended_references P Code); tauto].
Qed.
Definition active_ordered c := ordered (R.ranking (R.cfg_state c)) (active_owners (R.cfg_control c)).
Lemma ordered_drop order x xs : ordered order (x::xs) -> ordered order xs.
Proof. apply ordered_tail. Qed.
Lemma ordered_add_child order owner parents child :
  R.ranking_lt order owner child = true -> ordered order (owner::parents) -> ordered order (child::owner::parents).
Proof.
  intros Hlt Hsorted; inversion Hsorted as [|? ? Htail Hall]; subst; constructor; [exact Hsorted |].
  constructor; [exact Hlt |].
  eapply Forall_impl; [intros parent Hp; eapply lt_trans; [exact Hp |exact Hlt] |exact Hall].
Qed.

Ltac primitive_views :=
  repeat match goal with
  | H : R.complete_get _ _ _ = (_,_,_) |- _ =>
      let Hr := fresh "get_ranking" in let Ho := fresh "get_owner" in
      pose proof (get_rank H) as Hr; pose proof (get_owner H) as Ho; clear H
  | H : R.write_side_contribution _ _ _ _ = (_,_) |- _ =>
      let Hr := fresh "write_ranking" in pose proof (write_rank H) as Hr; clear H
  | H : R.set_value ?st ?fr ?direct = (?next,?next_fr) |- _ =>
      let Hv := fresh "view" in pose proof (@commit_footprint st fr direct next next_fr H) as Hv;
      let Hr := fresh "commit_ranking" in let Ho := fresh "commit_owner" in
      pose proof (commit_ranking Hv) as Hr; pose proof (commit_owner Hv) as Ho; clear H Hv
  end.
Theorem next_active_ordered tf support before after : config_wf support before ->
  active_ordered before -> step tf before after -> active_ordered after.
Proof.
  intros [Hst Hrefs] Hsorted Hstep.
  pose proof (@active_references (known support (R.cfg_state before)) support
    (R.cfg_control before) Hrefs) as Hknown.
  assert (Hranked : Forall (ranked (R.ranking (R.cfg_state before))) (active_owners (R.cfg_control before))).
  { eapply Forall_impl with (P := known support (R.cfg_state before)); [intros x Hx; exact (proj2 Hx) |exact Hknown]. }
  pose proof (@ordered_extend (R.ranking (R.cfg_state before)) (R.ranking (R.cfg_state after))
    (active_owners (R.cfg_control before)) (next_ranking_extends Hstep) Hranked Hsorted) as Hlift.
  destruct before as [st ctrl]; unfold step, R.next_config in Hstep; unfold active_ordered;
    cbn [R.cfg_state R.cfg_control] in Hstep, Hlift |- *.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep; primitive_views.
  all: cbn [R.cfg_state R.cfg_control active_owners suspended_owners R.frame_owner R.fresh_frame
    R.with_frame_side R.with_queue R.ranking R.requeue_changed_controlled_owner R.enqueue] in Hlift |- *.
  all: repeat match goal with Hr : R.frame_owner _ = R.frame_owner _ |- _ => rewrite Hr in *; clear Hr end.
  all: try exact Hlift; try solve [repeat constructor]; try solve [apply ordered_drop in Hlift; exact Hlift].
  all: repeat match goal with H : andb _ _ = true |- _ => apply andb_true_iff in H; destruct H end.
  all: unfold R.rank_lt in *;
    repeat rewrite materialize_rank in *; repeat rewrite close_rank in *;
    repeat match goal with Hr : R.ranking _ = R.ranking _ |- _ => rewrite Hr in *; clear Hr end;
    cbn [R.enqueue R.with_queue R.ranking R.with_frame_side R.frame_owner] in *;
    try exact Hlift; try solve [apply ordered_add_child; assumption].
Qed.
Theorem reachable_active_ordered tf roots c :
  steps tf (R.initial_config roots) c -> active_ordered c.
Proof.
  intro Hpath; assert (Hinitial : active_ordered (R.initial_config roots)) by constructor.
  assert (Hwf : config_wf (fun _ => True) (R.initial_config roots)) by (split; [apply store_initial |apply Forall_forall; auto]).
  revert Hwf Hinitial; induction Hpath; auto; intros Hwf Hsorted; apply IHHpath.
  - eapply next_configuration_wf; [intros owner _; apply code_unrestricted |exact Hwf |exact H].
  - eapply next_active_ordered; eauto.
Qed.
Lemma ordered_unique order owners : ordered order owners -> NoDup owners.
Proof.
  intro H; induction H; constructor; auto.
  intro Hin; rewrite Forall_forall in H0; pose proof (H0 a Hin) as Haa; rewrite lt_irrefl in Haa; discriminate.
Qed.
Corollary reachable_owners_unique tf roots c :
  steps tf (R.initial_config roots) c -> NoDup (active_owners (R.cfg_control c)).
Proof. intro H; apply (@ordered_unique (R.ranking (R.cfg_state c))); exact (@reachable_active_ordered tf roots c H). Qed.

Definition preserves_live before after := forall x, solved before x -> solved after x.
Lemma materialize_live st x : solved (R.materialize st x) x.
Proof.
  unfold R.materialize; destruct (M.lookup (R.sigma st) x) as [value|] eqn:H.
  - exists value; exact H.
  - exists D.bottom; cbn; apply ML.lookup_update_same.
Qed.
Lemma preserves_live_layout before after : R.sigma after = R.sigma before -> preserves_live before after.
Proof. intro H; intros x [value Hlookup]; exists value; change (M.lookup (R.sigma after) x = Some value); now rewrite H. Qed.
Lemma preserves_live_materialize st x : preserves_live st (R.materialize st x).
Proof.
  unfold R.materialize; destruct (M.lookup (R.sigma st) x); [intros y Hy; exact Hy |].
  intros y [value Hlookup]; destruct (V.eq_dec y x) as [-> |Hneq].
  - exists D.bottom; cbn; apply ML.lookup_update_same.
  - exists value; cbn; rewrite ML.lookup_update_other; auto.
Qed.
Lemma preserves_live_update st x value : preserves_live st (R.with_sigma st (M.update (R.sigma st) x value)).
Proof.
  intros y [old Hlookup]; destruct (V.eq_dec y x) as [-> |Hneq].
  - exists value; cbn; apply ML.lookup_update_same.
  - exists old; cbn; rewrite ML.lookup_update_other; auto.
Qed.
Lemma preserves_live_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  preserves_live st next /\ solved next target.
Proof.
  unfold R.complete_get; intro H; destruct (R.rank_lt st (R.frame_owner fr) target);
    inversion H; subst next next_fr value; split; try apply materialize_live.
  all: intros x Hx; apply preserves_live_materialize;
    eapply preserves_live_layout with (before := st); [reflexivity |exact Hx].
Qed.
Lemma preserves_live_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) -> preserves_live st next.
Proof.
  unfold R.set_value; intro H; split_program H; intros x Hx;
    try exact Hx.
  all: eapply preserves_live_layout with
    (before := R.with_sigma st (M.update (R.sigma st) (R.frame_owner fr) _));
    [reflexivity |eapply preserves_live_update; exact Hx].
Qed.
Arguments preserves_live_commit {st fr direct next next_fr} _.
Lemma next_preserves_live tf before after : step tf before after -> preserves_live (R.cfg_state before) (R.cfg_state after).
Proof.
  destruct before as [st ctrl]; unfold step, R.next_config; intro H;
    cbn [R.cfg_state R.cfg_control] in H |- *.
  destruct ctrl; cbn [R.cfg_control] in H;
    unfold R.continue_side, R.continue_dead in H; split_program H.
  all: repeat match goal with
  | Hget : R.complete_get _ _ _ = (_,_,_) |- _ =>
      let Hl := fresh "get_live" in pose proof (proj1 (preserves_live_get Hget)) as Hl; clear Hget
  | Hwrite : R.write_side_contribution _ _ _ _ = (_,_) |- _ =>
      let Hs := fresh "write_store" in pose proof (proj1 (proj2 (proj2 (write_layout Hwrite)))) as Hs; clear Hwrite
  | Hset : R.set_value _ _ _ = (_,_) |- _ =>
      let Hl := fresh "commit_live" in pose proof (preserves_live_commit Hset) as Hl; clear Hset
  end.
  all: unfold preserves_live; intros x Hx;
    cbn [R.cfg_state R.with_queue R.sigma R.enqueue R.requeue_changed_controlled_owner R.publish_targets] in *.
  all: try solve [eapply preserves_live_layout with (before := st); [reflexivity |exact Hx]].
  all: repeat match goal with
    | Hs : R.sigma ?next = R.sigma ?old |- solved ?next ?x =>
        eapply preserves_live_layout with (before := old); [exact Hs |]
    | Hl : preserves_live ?old ?next |- solved ?next ?x => apply Hl
    end.
  all: try solve [eapply preserves_live_layout with (before := st); [reflexivity |exact Hx]].
  all: try (apply preserves_live_materialize).
  all: unfold R.observe, R.reset_registered_cells, R.enqueue, R.with_queue;
    repeat match goal with
    | |- context [match Ranks.observe ?order ?target with _ => _ end] => destruct (Ranks.observe order target)
    | |- context [if ?b then _ else _] => destruct b
    end;
    try exact Hx;
    try solve [eapply preserves_live_layout with (before := st); [reflexivity |exact Hx]];
    try solve [apply preserves_live_materialize; eapply preserves_live_layout with (before := st); [reflexivity |exact Hx]].
  all: try solve [match goal with Hl : preserves_live ?old ?next |- _ =>
    eapply preserves_live_layout with (before := next); [reflexivity |apply Hl; exact Hx] end].
  all: match goal with Hs : R.sigma ?next = R.sigma ?old |- _ =>
    eapply preserves_live_layout with (before := next); [reflexivity |];
    eapply preserves_live_layout with (before := old); [exact Hs |] end.
  all: unfold R.observe; repeat match goal with
    | |- context [match Ranks.observe ?order ?target with _ => _ end] => destruct (Ranks.observe order target)
    end; exact Hx.

Qed.
Lemma steps_preserve_live tf before after : steps tf before after -> preserves_live (R.cfg_state before) (R.cfg_state after).
Proof. intro H; induction H; intros x Hx; auto; apply IHsteps; eapply next_preserves_live; eauto. Qed.

Definition framed_owners ctrl :=
  match ctrl with
  | R.StartEpisode _ k => suspended_owners k
  | _ => active_owners ctrl
  end.
Definition frames_live c := Forall (solved (R.cfg_state c)) (framed_owners (R.cfg_control c)).
Theorem next_frames_live tf before after : frames_live before -> step tf before after -> frames_live after.
Proof.
  intros Hlive Hstep.
  assert (Hlift : Forall (solved (R.cfg_state after)) (framed_owners (R.cfg_control before))).
  { eapply Forall_impl with (P := solved (R.cfg_state before)); [intros x Hx; eapply next_preserves_live; eauto |exact Hlive]. }
  destruct before as [st ctrl]; unfold step, R.next_config in Hstep; unfold frames_live;
    cbn [R.cfg_state R.cfg_control] in Hstep, Hlift |- *.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep; primitive_views.
  all: cbn [R.cfg_state R.cfg_control active_owners framed_owners suspended_owners
    R.frame_owner R.fresh_frame R.with_frame_side] in Hlift |- *.
  all: repeat match goal with Hr : R.frame_owner _ = R.frame_owner _ |- _ => rewrite Hr in *; clear Hr end.
  all: try exact Hlift; try solve [constructor]; try solve [inversion Hlift; assumption].
  all: constructor; [apply materialize_live |exact Hlift].
Qed.
Theorem reachable_frames_live tf roots c : steps tf (R.initial_config roots) c -> frames_live c.
Proof.
  intro Hpath; assert (Hinitial : frames_live (R.initial_config roots)) by constructor.
  revert Hinitial; induction Hpath; auto; intro Hfirst; apply IHHpath; eapply next_frames_live; eauto.
Qed.
Lemma materialize_queue st x : R.queue (R.materialize st x) = R.queue st.
Proof. unfold R.materialize; destruct (M.lookup (R.sigma st) x); reflexivity. Qed.
Lemma close_queue st x : R.queue (R.reset_registered_cells st x) = R.queue st.
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity. Qed.
Lemma observe_queue st x : R.queue (R.observe st x) = R.queue st.
Proof. unfold R.observe; destruct (Ranks.observe _ _); reflexivity. Qed.
Lemma get_queue st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) -> R.queue next = R.queue st.
Proof. intro H; exact (proj1 (proj2 (get_layout H))). Qed.
Lemma write_queue st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) -> R.queue next = R.queue st.
Proof. intro H; exact (proj1 (proj2 (write_layout H))). Qed.
Lemma commit_keeps_queue st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  forall x, In x (R.queue st) -> In x (R.queue next).
Proof.
  intros Hset x Hin; destruct (@commit_queue st fr direct next next_fr Hset) as [Hq |Hq]; rewrite Hq; auto.
  apply insert_all_members; auto.
Qed.
Arguments commit_keeps_queue {st fr direct next next_fr} _ x _.
Lemma requeue_keeps_queue before after owner x : In x (R.queue after) ->
  In x (R.queue (R.requeue_changed_controlled_owner before after owner)).
Proof.
  intro Hin; unfold R.requeue_changed_controlled_owner; cbn;
    destruct (Features.recompute_controlled && S.mem owner (R.controlled before) &&
      negb (R.equivalent (R.sigma_value after owner) (R.sigma_value before owner)))%bool; auto.
  apply insert_members; auto.
Qed.
Lemma popped_members queue owner rest x : R.queue_pop queue = Some (owner,rest) -> In x queue -> x = owner \/ In x rest.
Proof. destruct queue; cbn; intros H Hin; [discriminate |inversion H; subst; intuition]. Qed.
Lemma peek_popped queue owner rest : R.queue_pop queue = Some (owner,rest) -> R.queue_peek queue = Some owner.
Proof. destruct queue; cbn; intro H; [discriminate |inversion H; reflexivity]. Qed.
Lemma next_queue_covered tf before after : step tf before after -> forall x,
  In x (R.queue (R.cfg_state before)) ->
  In x (R.queue (R.cfg_state after)) \/ In x (active_owners (R.cfg_control after)).
Proof.
  destruct before as [st ctrl]; unfold step, R.next_config; intro H;
    cbn [R.cfg_state R.cfg_control] in H |- *.
  destruct ctrl; cbn [R.cfg_control] in H;
    unfold R.continue_side, R.continue_dead, R.record_side_input in H; split_program H.
  all: repeat match goal with
  | Hget : R.complete_get _ _ _ = (_,_,_) |- _ => let Hq := fresh "get_queue" in pose proof (get_queue Hget) as Hq; clear Hget
  | Hwrite : R.write_side_contribution _ _ _ _ = (_,_) |- _ => let Hq := fresh "write_queue" in pose proof (write_queue Hwrite) as Hq; clear Hwrite
  end.
  all: intros x Hin; cbn [R.cfg_state R.cfg_control active_owners suspended_owners
    R.with_queue R.queue R.enqueue R.frame_owner R.fresh_frame] in *;
    repeat first [rewrite materialize_queue |rewrite close_queue |rewrite observe_queue |
      match goal with Hq : R.queue _ = _ |- _ => rewrite Hq; clear Hq end |
      progress cbn [R.enqueue R.with_queue R.queue]].
  all: repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    repeat first [rewrite materialize_queue |rewrite close_queue |rewrite observe_queue |
      progress cbn [R.enqueue R.with_queue R.queue]].
  all: try solve [left; exact Hin]; try solve [left; apply insert_members; auto].
  all: try solve [left; apply requeue_keeps_queue; eapply commit_keeps_queue; eauto].
  all: repeat match goal with Hpeek : R.queue_peek ?queue = Some ?owner,
    Hpop : R.queue_pop ?queue = Some (?head,?rest) |- _ =>
      let Hp := fresh "peek_pop" in pose proof (@peek_popped queue head rest Hpop) as Hp;
      assert (head = owner) by congruence; subst head; clear Hp Hpeek end.
  all: try solve [match goal with Hpop : R.queue_pop ?q = Some (?head,?rest) |- _ =>
      destruct (@popped_members q head rest x Hpop Hin) as [-> |Htail]; [right; left; reflexivity |left; exact Htail] end].
Qed.

Fixpoint suspended_roots k : list V.t :=
  match k with
  | R.KLoop => []
  | R.KSeedLoop roots => roots
  | R.KAfterGet _ _ _ rest |R.KAfterSide _ _ rest |R.KAfterSpawn _ _ rest
  | R.KDead _ _ _ rest |R.KDrain _ rest => suspended_roots rest
  end.
Definition pending_roots ctrl :=
  match ctrl with
  | R.RunLoop => []
  | R.RunSeeds roots |R.RunSeedLoop roots => roots
  | R.StartEpisode _ k |R.RunRhs _ _ k |R.RunDead _ _ _ k
  | R.RunCommit _ _ k |R.RunDrain _ k |R.Return k => suspended_roots k
  end.
Definition covered_roots roots c := forall x, In x roots -> solved (R.cfg_state c) x \/
  In x (R.queue (R.cfg_state c)) \/ In x (active_owners (R.cfg_control c)) \/ In x (pending_roots (R.cfg_control c)).
Lemma materialized_solved st x : R.is_materialized st x = true -> solved st x.
Proof. unfold R.is_materialized; destruct (M.lookup (R.sigma st) x) as [value|] eqn:H; [exists value; exact H |discriminate]. Qed.
Lemma next_work_covered tf before after : frames_live before -> step tf before after -> forall x,
  In x (active_owners (R.cfg_control before)) \/ In x (pending_roots (R.cfg_control before)) ->
  solved (R.cfg_state after) x \/ In x (active_owners (R.cfg_control after)) \/ In x (pending_roots (R.cfg_control after)).
Proof.
  intros Hlive Hstep.
  assert (Hlift : Forall (solved (R.cfg_state after)) (framed_owners (R.cfg_control before))).
  { eapply Forall_impl with (P := solved (R.cfg_state before)); [intros x Hx; eapply next_preserves_live; eauto |exact Hlive]. }
  destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep, Hlift |- *.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep; primitive_views.
  all: cbn [R.cfg_state R.cfg_control active_owners framed_owners suspended_owners pending_roots suspended_roots
    R.frame_owner R.fresh_frame R.with_frame_side] in Hlift |- *.
  all: repeat match goal with Hr : R.frame_owner _ = R.frame_owner _ |- _ => rewrite Hr in *; clear Hr end.
  all: rewrite Forall_forall in Hlift; intros x Hin; cbn in Hin |- *;
    try solve [intuition eauto].
  all: try match goal with Hmat : R.is_materialized _ _ = true |- _ => apply materialized_solved in Hmat end;
    cbn in Hlift; intuition eauto.
  all: subst; auto.
Qed.
Lemma next_roots_covered tf roots before after : frames_live before -> covered_roots roots before ->
  step tf before after -> covered_roots roots after.
Proof.
  intros Hlive Hroots Hstep x Hx; destruct (Hroots x Hx) as [Hsolved |[Hqueue |[Hactive |Hpending]]].
  - left; eapply next_preserves_live; eauto.
  - destruct (@next_queue_covered tf before after Hstep x Hqueue) as [Hqueue' |Hactive']; auto.
  - destruct (@next_work_covered tf before after Hlive Hstep x (or_introl Hactive)) as [Hsolved' |[Hactive' |Hpending']]; auto.
  - destruct (@next_work_covered tf before after Hlive Hstep x (or_intror Hpending)) as [Hsolved' |[Hactive' |Hpending']]; auto.
Qed.
Theorem reachable_roots_covered tf roots c : steps tf (R.initial_config roots) c -> covered_roots roots c.
Proof.
  intro Hpath; assert (Hinitial : covered_roots roots (R.initial_config roots)) by (intros x Hx; right; right; right; exact Hx).
  assert (Hlive : frames_live (R.initial_config roots)) by constructor.
  revert Hlive Hinitial; induction Hpath; auto; intros Hlive Hfirst; apply IHHpath.
  - eapply next_frames_live; eauto.
  - eapply next_roots_covered; eauto.
Qed.
Theorem successful_roots_materialized fuel tf roots final : R.solve_fuel fuel tf roots = Some final ->
  forall x, In x roots -> solved final x.
Proof.
  intro Hrun; destruct (@successful_path fuel tf roots final Hrun) as [Hpath Hqueue].
  pose proof (@reachable_roots_covered tf roots (terminal final) Hpath) as Hroots.
  intros x Hx; destruct (Hroots x Hx) as [Hsolved |[Hqueued |[Hactive |Hpending]]]; [exact Hsolved | |contradiction |contradiction].
  change (In x (R.queue final)) in Hqueued; rewrite Hqueue in Hqueued; contradiction.
Qed.

Lemma materialize_lookup st target observed value : M.lookup (R.sigma st) observed = Some value ->
  M.lookup (R.sigma (R.materialize st target)) observed = Some value.
Proof.
  intro H; unfold R.materialize; destruct (M.lookup (R.sigma st) target) eqn:Ht; auto.
  cbn; destruct (V.eq_dec observed target) as [-> |Hneq].
  - rewrite Ht in H; discriminate.
  - rewrite ML.lookup_update_other; auto.
Qed.
Lemma materialize_value st target :
  M.lookup (R.sigma (R.materialize st target)) target = Some (R.sigma_value (R.materialize st target) target).
Proof.
  unfold R.materialize; destruct (M.lookup (R.sigma st) target) as [value|] eqn:Ht;
    unfold R.sigma_value; cbn; rewrite ?ML.lookup_update_same, ?Ht; reflexivity.
Qed.
Lemma materialize_readers st target : R.readers (R.materialize st target) = R.readers st.
Proof. unfold R.materialize; destruct (M.lookup (R.sigma st) target); reflexivity. Qed.
Lemma watched_layout before after owner reads : R.sigma after = R.sigma before -> R.readers after = R.readers before ->
  watched_reads before owner reads -> watched_reads after owner reads.
Proof. intros Hs Hr H target value Hin; unfold watched_reads in H |- *; rewrite Hs, Hr; exact (H target value Hin). Qed.
Lemma watched_materialize st target owner reads : watched_reads st owner reads -> watched_reads (R.materialize st target) owner reads.
Proof.
  intros H observed value Hin; destruct (H observed value Hin) as [Hv Hr]; split.
  - apply materialize_lookup; exact Hv.
  - rewrite materialize_readers; exact Hr.
Qed.
Lemma reader_added_preserves readers target source owner observed : S.mem owner (R.lookup_set readers observed) = true ->
  S.mem owner (R.lookup_set (M.update readers target (S.add source (R.lookup_set readers target))) observed) = true.
Proof.
  intro H; unfold R.lookup_set; destruct (V.eq_dec observed target) as [-> |Hneq].
  - rewrite ML.lookup_update_same; apply SL.add_spec; right; exact H.
  - rewrite ML.lookup_update_other; auto.
Qed.
Lemma watched_add_reader st target source owner reads : watched_reads st owner reads ->
  watched_reads (R.with_readers st (M.update (R.readers st) target
    (S.add source (R.lookup_set (R.readers st) target)))) owner reads.
Proof.
  intros H observed value Hin; destruct (H observed value Hin) as [Hv Hr]; split; [exact Hv |].
  apply reader_added_preserves; exact Hr.
Qed.
Lemma watched_get st fr target next next_fr value owner reads : R.complete_get st fr target = (next,next_fr,value) ->
  watched_reads st owner reads -> watched_reads next owner reads.
Proof.
  unfold R.complete_get; intros H Hreads; destruct (R.rank_lt st (R.frame_owner fr) target);
    inversion H; subst next next_fr value; apply watched_materialize;
    intros observed raw Hin; destruct (Hreads observed raw Hin) as [Hv Hr]; split;
    [exact Hv |apply reader_added_preserves; exact Hr |exact Hv |apply reader_added_preserves; exact Hr].
Qed.
Lemma get_watches_target st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  M.lookup (R.sigma next) target = Some value /\ S.mem (R.frame_owner fr) (R.lookup_set (R.readers next) target) = true.
Proof.
  unfold R.complete_get; intro H; destruct (R.rank_lt st (R.frame_owner fr) target);
    inversion H; subst next next_fr value; split; [apply materialize_value | |apply materialize_value |];
    rewrite materialize_readers; unfold R.lookup_set; cbn; rewrite ML.lookup_update_same; apply SL.add_spec; auto.
Qed.
Definition invalidate_value st owner value :=
  let st1 := R.with_sigma st (M.update (R.sigma st) owner value) in
  let st2 := R.enqueue_all st1 (S.elements (R.lookup_set (R.readers st1) owner)) in
  R.with_readers st2 (M.update (R.readers st2) owner S.empty).
Lemma watched_invalidation st owner value reader reads : watched_reads st reader reads ->
  ~ In reader (R.queue (invalidate_value st owner value)) -> watched_reads (invalidate_value st owner value) reader reads.
Proof.
  intros Hreads Hquiet target observed Hin; destruct (Hreads target observed Hin) as [Hvalue Hregistered].
  destruct (V.eq_dec target owner) as [-> |Hneq].
  - exfalso; apply Hquiet; unfold invalidate_value; cbn; apply insert_all_members; left; apply SL.mem_spec; exact Hregistered.
  - split; unfold invalidate_value; cbn.
    + rewrite ML.lookup_update_other; auto.
    + unfold R.lookup_set; rewrite ML.lookup_update_other; auto.
Qed.
Lemma watched_commit st fr direct next next_fr reader reads : R.set_value st fr direct = (next,next_fr) ->
  watched_reads st reader reads -> ~ In reader (R.queue next) -> watched_reads next reader reads.
Proof.
  unfold R.set_value; intros H Hreads Hquiet; split_program H; try exact Hreads.
  all: eapply watched_invalidation; [exact Hreads |exact Hquiet].
Qed.
Lemma watched_snoc st owner reads target value : watched_reads st owner reads ->
  M.lookup (R.sigma st) target = Some value -> S.mem owner (R.lookup_set (R.readers st) target) = true ->
  watched_reads st owner (reads ++ [(target,value)]).
Proof.
  intros Hreads Hvalue Hregistered observed raw Hin; apply in_app_or in Hin; destruct Hin as [Hin |[Heq |Hin]];
    [apply Hreads; exact Hin |inversion Heq; subst; auto |contradiction].
Qed.

Lemma termination_has_fuel tf roots final : terminates_to tf roots final ->
  exists fuel, R.solve_fuel fuel tf roots = Some final.
Proof.
  intros [Hpath Hquiet]; destruct (path_fuel Hpath) as [fuel Hfuel]; exists fuel.
  unfold R.solve_fuel; rewrite Hfuel; unfold R.terminal_state, terminal, R.queue_peek; cbn; now rewrite Hquiet.
Qed.
Lemma termination_iff_fuel tf roots :
  (exists final, terminates_to tf roots final) <-> (exists fuel final, R.solve_fuel fuel tf roots = Some final).
Proof.
  split; [intros [final Hfinal]; destruct (termination_has_fuel Hfinal) as [fuel Hrun]; eauto |].
  intros [fuel [final Hrun]]; exists final; exact (@successful_path fuel tf roots final Hrun).
Qed.
Lemma monotonic_system_on tf support : monotonic_system tf -> Sem.system_monotone_on tf support.
Proof. intro H; constructor; intros owner Howner; exact (proj1 (H owner)) ||exact (proj2 (H owner)). Qed.
Lemma supported_spawns P body result : Sem.rhs_supported P body -> Sem.rhs_observes body result ->
  forall target, In target (Sem.observed_spawns result) -> P target.
Proof.
  intros Hcode Hobs; revert Hcode; induction Hobs; intro Hcode;
    pose proof (code_child_supported Hcode) as Hchildren; cbn in Hchildren; intros observed Hin; cbn in Hin.
  - contradiction.
  - eapply IHHobs; [apply (proj2 Hchildren) |exact Hin].
  - eapply IHHobs; [exact (proj2 Hchildren) |exact Hin].
  - destruct Hin as [<- |Hin]; [exact (proj1 Hchildren) |eapply IHHobs; [exact (proj2 Hchildren) |exact Hin]].
Qed.
Lemma owner_post_observation tf st owner : owner_post_solution tf st owner ->
  forall result, Sem.observes_at (R.sigma_value st) (tf owner) result ->
    D.leq (Sem.observed_direct result) (R.sigma_value st owner) = true /\
    Sem.valuation_side_effects_below (R.sigma_value st) (Sem.observed_sides result).
Proof.
  intros [[direct [reads [sides Hreplay]]] [Hvalues Hspawns]] result Hat.
  destruct (replay_observation Hreplay) as [actual [Hactual [Hd [Hr Hs]]]].
  assert (Heq : actual = result) by (eapply observation_unique; eauto); subst actual.
  rewrite Hd, Hs; exact (Hvalues direct reads sides Hreplay).
Qed.
Lemma solved_dec st x : {solved st x} + {~ solved st x}.
Proof.
  destruct (M.lookup (R.sigma st) x) as [value|] eqn:H.
  - left; exists value; exact H.
  - right; intros [value Hv]; change (M.lookup (R.sigma st) x = Some value) in Hv; congruence.
Qed.
Lemma unsolved_bottom st x : ~ solved st x -> R.sigma_value st x = D.bottom.
Proof.
  intro H; unfold R.sigma_value; destruct (M.lookup (R.sigma st) x) as [value|] eqn:Hv; auto;
    exfalso; apply H; exists value; exact Hv.
Qed.
Module Strict := SourceStrictness.Make V D DL.
Definition source_strict_on := Strict.source_strict_on Sem.observes_at Sem.observed_direct Sem.observed_sides.
Lemma correct_source_strict_solution tf roots (finite : Sem.finite_system tf roots) final :
  source_strict_on tf (Sem.support finite) roots -> correct_final_state tf roots final ->
  Sem.post_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
  intros Hstrict [Hroots Hlocal] owner Hin result Hat; split.
  - destruct (solved_dec final owner) as [Hsolved |Hunsolved].
    + exact (proj1 (owner_post_observation (Hlocal owner Hsolved) Hat)).
    + assert (Hnotroot : ~ In owner roots) by (intro Hroot; apply Hunsolved; apply Hroots; exact Hroot).
      destruct (Hstrict owner Hin Hnotroot (R.sigma_value final) result Hat
        ltac:(rewrite (unsolved_bottom Hunsolved); apply DL.leq_refl)) as [Hdirect Hsides].
      eapply DL.leq_trans; [exact Hdirect |apply DL.bottom_least].
  - split.
    + destruct (solved_dec final owner) as [Hsolved |Hunsolved].
      * exact (proj2 (owner_post_observation (Hlocal owner Hsolved) Hat)).
      * assert (Hnotroot : ~ In owner roots) by (intro Hroot; apply Hunsolved; apply Hroots; exact Hroot).
        destruct (Hstrict owner Hin Hnotroot (R.sigma_value final) result Hat
          ltac:(rewrite (unsolved_bottom Hunsolved); apply DL.leq_refl)) as [Hdirect Hsides].
        intros target raw Hraw; eapply DL.leq_trans; [exact (Hsides target raw Hraw) |apply DL.bottom_least].
    + intros target Htarget; eapply (@supported_spawns (fun x => In x (Sem.support finite)) (tf owner) result); [apply Sem.system_supported; exact Hin |exact (proj1 Hat) |exact Htarget].
Qed.

(** A semantic bridge: source strictness supplies the complete post-solution,
    while the operational proof below supplies final correctness. *)
Theorem correct_successful_run_least fuel tf roots (finite : Sem.finite_system tf roots) final :
  (forall side x phase old input upper, D.leq old upper = true -> D.leq input upper = true ->
    D.leq (snd (U.update side x phase old input)) upper = true) ->
  source_strict_on tf (Sem.support finite) roots -> Sem.system_monotone_on tf (Sem.support finite) ->
  correct_final_state tf roots final -> R.solve_fuel fuel tf roots = Some final ->
  Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
  intros Hbounded Hstrict Hmono Hcorrect Hrun; split.
  - eapply correct_source_strict_solution; eauto.
  - intros upper Hupper owner Hin; exact (@successful_run_below Hbounded fuel tf roots finite final upper Hmono Hupper Hrun owner).
Qed.

Lemma write_contribution_sound st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  D.leq input (R.stored_contribution next (R.frame_owner fr) target) = true.
Proof.
  unfold R.write_side_contribution; intro H.
  set (st0 := R.promote_side_target st fr target) in *.
  pose proof (@UL.update_sound true target (R.side_phase (R.stored_side_cell st0 (R.frame_owner fr) target))
    (R.stored_contribution st0 (R.frame_owner fr) target) input) as Hsound.
  inversion H; subst next changed; unfold R.stored_contribution, R.register_reset; cbn.
  unfold R.update_map, R.lookup_map; rewrite !ML.lookup_update_same; exact Hsound.
Qed.
Lemma write_other_contribution st fr target input next changed source observed :
  R.write_side_contribution st fr target input = (next,changed) ->
  (observed <> target \/ source <> R.frame_owner fr) ->
  R.stored_contribution next source observed = R.stored_contribution st source observed.
Proof.
  unfold R.write_side_contribution; intros H Hother; inversion H; subst next changed.
  unfold R.stored_contribution, R.register_reset, R.promote_side_target; cbn.
  destruct (R.rank_lt st target (R.frame_owner fr)); cbn; destruct Hother as [Htarget |Hsource].
  all: try (rewrite row_other; auto; reflexivity).
  all: destruct (V.eq_dec observed target) as [-> |Hneq]; [|rewrite row_other; auto; reflexivity].
  all: unfold R.update_map, R.lookup_map; rewrite ML.lookup_update_same, ML.lookup_update_other; auto.
Qed.

Definition quiet_reads st owner reads := ~ In owner (R.queue st) -> watched_reads st owner reads.
Record evaluated_observation tf st owner direct := {
  evaluated_reads : list (V.t * D.t);
  evaluated_sides : list (V.t * D.t);
  evaluated_spawns : list V.t;
  evaluated_trace : Sem.rhs_observes (tf owner)
    {| Sem.Observation.observed_direct := direct;
       Sem.Observation.observed_reads := evaluated_reads;
       Sem.Observation.observed_sides := evaluated_sides;
       Sem.Observation.observed_spawns := evaluated_spawns |};
  evaluated_watches : quiet_reads st owner evaluated_reads;
  evaluated_side_bounds : forall target raw, In (target,raw) evaluated_sides ->
    D.leq raw (R.stored_contribution st owner target) = true;
  evaluated_spawn_bounds : forall target, In target evaluated_spawns -> solved st target
}.

(** The ordinary/side update result gives its bound even when no value is
    written. Read invalidation and the optional self-entry ensure that a quiet
    owner retains a replayable observation at the committed value. *)
Lemma commit_completed_observation tf st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) ->
  evaluated_observation tf st (R.frame_owner fr) direct ->
  ~ In (R.frame_owner fr) (R.queue (R.requeue_changed_controlled_owner st next (R.frame_owner fr))) ->
  completed_observation tf (R.requeue_changed_controlled_owner st next (R.frame_owner fr)) (R.frame_owner fr).
Proof.
  intros Hset evaluated Hquiet.
  pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview.
  assert (Hnext : ~ In (R.frame_owner fr) (R.queue next)).
  { intro Hin; apply Hquiet; apply requeue_keeps_queue; exact Hin. }
  assert (Hbefore : ~ In (R.frame_owner fr) (R.queue st)).
  { intro Hin; apply Hnext; exact (commit_keeps_queue Hset (R.frame_owner fr) Hin). }
  destruct evaluated as [reads sides spawns Htrace Hreads Hsides Hspawns].
  refine {| completed_result :=
    {| Sem.Observation.observed_direct := direct;
       Sem.Observation.observed_reads := reads;
       Sem.Observation.observed_sides := sides;
       Sem.Observation.observed_spawns := spawns |};
    completed_trace := Htrace |}.
  - eapply watched_layout with (before := next); [reflexivity |reflexivity |].
    eapply watched_commit; [exact Hset |apply Hreads; exact Hbefore |exact Hnext].
  - eapply DL.leq_trans; [apply DL.join_upper_left |].
    exact (@commit_sound st fr direct next next_fr Hset).
  - intros target raw Hin; change (D.leq raw (R.stored_contribution next (R.frame_owner fr) target) = true).
    unfold R.stored_contribution; rewrite (commit_contributions Hview); apply Hsides; exact Hin.
  - intros target Hin; eapply preserves_live_layout with (before := next); [reflexivity |].
    eapply preserves_live_commit; [exact Hset |apply Hspawns; exact Hin].
Qed.

Lemma quiet_controlled_commit st next owner : Features.recompute_controlled = true ->
  S.mem owner (R.controlled st) = true ->
  ~ In owner (R.queue (R.requeue_changed_controlled_owner st next owner)) ->
  eqv (R.sigma_value next owner) (R.sigma_value st owner).
Proof.
  intros Hon Hcontrolled Hquiet; apply eqv_bool.
  destruct (R.equivalent (R.sigma_value next owner) (R.sigma_value st owner)) eqn:Hvalue; auto.
  exfalso; apply Hquiet; eapply requeue_if_changed; eauto.
Qed.
Arguments quiet_controlled_commit {st next owner} _ _ _.
Lemma quiet_commit_update st fr direct next next_fr : Features.recompute_controlled = true ->
  S.mem (R.frame_owner fr) (R.controlled st) = true -> R.set_value st fr direct = (next,next_fr) ->
  ~ In (R.frame_owner fr) (R.queue (R.requeue_changed_controlled_owner st next (R.frame_owner fr))) ->
  eqv (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) \/
  eqv (snd (U.update false (R.frame_owner fr) (R.frame_phase fr)
    (R.sigma_value st (R.frame_owner fr)) (D.join direct (R.aggregate st (R.frame_owner fr)))))
    (R.sigma_value st (R.frame_owner fr)).
Proof.
  intros Hon Hcontrolled Hset Hquiet.
  pose proof (quiet_controlled_commit (owner := R.frame_owner fr) Hon Hcontrolled Hquiet) as Hsame.
  unfold R.set_value in Hset; destruct (R.equivalent _ _) eqn:Hcandidate.
  - left; apply eqv_bool; exact Hcandidate.
  - right; rewrite Hcontrolled in Hset.
    destruct (U.update _ _ _ _ _) as [phase value] eqn:Hupdate; cbn in Hset |- *.
    destruct (R.equivalent value (R.sigma_value st (R.frame_owner fr))) eqn:Hvalue.
    + apply eqv_bool; exact Hvalue.
    + inversion Hset; subst next next_fr; unfold R.sigma_value in Hsame; cbn in Hsame.
      rewrite ML.lookup_update_same in Hsame; exact Hsame.
Qed.
Section NarrowingCommit.
Variable narrow : D.t -> D.t -> D.t.
Variable safe_phase : U.phase -> Prop.
Variable update_is_narrow : forall owner phase old input, safe_phase phase -> D.leq input old = true ->
  snd (U.update false owner phase old input) = narrow old input.
Variable narrow_lower : forall old input, D.leq input old = true -> D.leq input (narrow old input) = true.
Variable narrow_upper : forall old input, D.leq input old = true -> D.leq (narrow old input) old = true.

(** A quiet commit supplies the local equation. The ordinary precision
    invariant below retains its observation until the final store. *)
Theorem quiet_commit_narrowing_fixed st fr direct next next_fr : Features.recompute_controlled = true ->
  safe_phase (R.frame_phase fr) -> S.mem (R.frame_owner fr) (R.controlled st) = true ->
  R.set_value st fr direct = (next,next_fr) ->
  ~ In (R.frame_owner fr) (R.queue (R.requeue_changed_controlled_owner st next (R.frame_owner fr))) ->
  eqv (narrow (R.sigma_value st (R.frame_owner fr)) (D.join direct (R.aggregate st (R.frame_owner fr))))
    (R.sigma_value st (R.frame_owner fr)).
Proof.
  intros Hon Hsafe Hcontrolled Hset Hquiet.
  destruct (@quiet_commit_update st fr direct next next_fr Hon Hcontrolled Hset Hquiet) as [[Hinput Hold] |Hstutter].
  - split; [apply narrow_upper; exact Hinput |].
    eapply DL.leq_trans; [exact Hold |apply narrow_lower; exact Hinput].
  - assert (Hinput : D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true).
    { eapply DL.leq_trans; [exact (@commit_sound st fr direct next next_fr Hset) |].
      exact (proj1 (quiet_controlled_commit Hon Hcontrolled Hquiet)). }
    rewrite <- (@update_is_narrow (R.frame_owner fr) (R.frame_phase fr)
      (R.sigma_value st (R.frame_owner fr)) _ Hsafe Hinput); exact Hstutter.
Qed.
End NarrowingCommit.

(** A frame carries a prefix of its original constraint. The ledger connects
    raw side effects to accumulated inputs, rather than relying on monotonic
    side updates. Dead-side cleanup cannot touch a ledger entry. *)
Definition side_ledger st fr := forall target input,
  M.lookup (R.frame_local_side fr) target = Some input ->
  S.mem target (R.frame_current_targets fr) = true /\
  D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true.
Record cursor tf (live : V.t -> Prop) st fr body := {
  cursor_reads : list (V.t * D.t);
  cursor_sides : list (V.t * D.t);
  cursor_spawns : list V.t;
  cursor_prefix : observation_prefix (tf (R.frame_owner fr)) body cursor_reads cursor_sides cursor_spawns;
  cursor_watches : quiet_reads st (R.frame_owner fr) cursor_reads;
  cursor_raw : forall target raw, In (target,raw) cursor_sides ->
    exists input, M.lookup (R.frame_local_side fr) target = Some input /\ D.leq raw input = true;
  cursor_ledger : side_ledger st fr;
  cursor_live : forall target, In target cursor_spawns -> live target
}.

Lemma cursor_fresh tf live st owner phase : cursor tf live st (R.fresh_frame st owner phase) (tf owner).
Proof.
  refine {| cursor_reads := []; cursor_sides := []; cursor_spawns := [] |}.
  - apply prefix_fresh.
  - intros _ target value Hin; contradiction.
  - intros target raw Hin; contradiction.
  - intros target input Hlookup; cbn [R.fresh_frame R.frame_local_side] in Hlookup;
      rewrite ML.lookup_empty in Hlookup; discriminate.
  - intros target Hin; contradiction.
Qed.

Lemma cursor_transfer tf P Q st next fr next_fr body :
  R.frame_owner next_fr = R.frame_owner fr ->
  R.frame_local_side next_fr = R.frame_local_side fr ->
  R.frame_current_targets next_fr = R.frame_current_targets fr ->
  (forall reads, quiet_reads st (R.frame_owner fr) reads -> quiet_reads next (R.frame_owner fr) reads) ->
  (forall target, R.stored_contribution next (R.frame_owner fr) target =
    R.stored_contribution st (R.frame_owner fr) target) ->
  (forall target, P target -> Q target) -> cursor tf P st fr body -> cursor tf Q next next_fr body.
Proof.
  intros Ho Hl Hc Hw Hs HP [reads sides spawns Hprefix Hreads Hraw Hledger Hlive].
  refine {| cursor_reads := reads; cursor_sides := sides; cursor_spawns := spawns |}.
  - rewrite Ho; exact Hprefix.
  - rewrite Ho; apply Hw; exact Hreads.
  - rewrite Hl; exact Hraw.
  - intros target input Hlookup; rewrite Hl in Hlookup; rewrite Hc, Ho, Hs; apply Hledger; exact Hlookup.
  - intros target Hin; apply HP; apply Hlive; exact Hin.
Qed.

Definition quiet_preserving before after := forall owner reads,
  quiet_reads before owner reads -> quiet_reads after owner reads.
Lemma quiet_layout before after : R.sigma after = R.sigma before ->
  R.readers after = R.readers before ->
  (forall owner, In owner (R.queue before) -> In owner (R.queue after)) -> quiet_preserving before after.
Proof.
  intros Hs Hr Hq owner reads Hreads Hquiet; eapply watched_layout; [exact Hs |exact Hr |].
  apply Hreads; intro Hin; apply Hquiet; apply Hq; exact Hin.
Qed.
Lemma quiet_materialize st target : quiet_preserving st (R.materialize st target).
Proof. intros owner reads H Hq; apply watched_materialize; apply H; rewrite (materialize_queue st target) in Hq; exact Hq. Qed.
Lemma quiet_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) -> quiet_preserving st next.
Proof.
  intros Hget owner reads H Hq; eapply watched_get; [exact Hget |apply H; rewrite <- (get_queue Hget); exact Hq].
Qed.
Lemma quiet_set st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) -> quiet_preserving st next.
Proof.
  intros Hset owner reads H Hq; eapply watched_commit; [exact Hset |apply H |exact Hq].
  intro Hin; apply Hq; eapply commit_keeps_queue; eauto.
Qed.
Lemma quiet_pop st head rest owner reads : R.queue st = head :: rest -> owner <> head ->
  quiet_reads st owner reads -> quiet_reads (R.with_queue st rest) owner reads.
Proof.
  intros Hqueue Hneq H Hquiet; apply H; rewrite Hqueue; intros [Heq |Hin]; [congruence |apply Hquiet; exact Hin].
Qed.

Lemma cursor_get tf live st fr target next next_fr value tail :
  R.complete_get st fr target = (next,next_fr,value) ->
  cursor tf live st fr (Syntax.Get target tail) -> cursor tf live next next_fr (tail value).
Proof.
  intros Hget [reads sides spawns Hprefix Hreads Hraw Hledger Hlive].
  pose proof (get_layout Hget) as [Hrank [Hqueue [Hcontrib [Hcells [Hresets [Htargets Howner]]]]]].
  assert (Hlocal : R.frame_local_side next_fr = R.frame_local_side fr).
  { unfold R.complete_get in Hget; split_program Hget; reflexivity. }
  assert (Hcurrent : R.frame_current_targets next_fr = R.frame_current_targets fr).
  { unfold R.complete_get in Hget; split_program Hget; reflexivity. }
  refine {| cursor_reads := reads ++ [(target,value)]; cursor_sides := sides; cursor_spawns := spawns |}.
  - rewrite Howner; apply prefix_get; exact Hprefix.
  - rewrite Howner; intros Hquiet; apply watched_snoc.
    + apply (quiet_get Hget Hreads); exact Hquiet.
    + exact (proj1 (get_watches_target Hget)).
    + exact (proj2 (get_watches_target Hget)).
  - rewrite Hlocal; exact Hraw.
  - intros observed input Hlookup; rewrite Hlocal in Hlookup; rewrite Hcurrent, Howner;
      unfold R.stored_contribution; rewrite Hcontrib; exact (Hledger observed input Hlookup).
  - exact Hlive.
Qed.

Lemma cursor_spawn tf live st fr target tail : live target ->
  cursor tf live st fr (Syntax.Spawn target tail) -> cursor tf live st fr tail.
Proof.
  intros Htarget [reads sides spawns Hprefix Hreads Hraw Hledger Hlive].
  refine {| cursor_reads := reads; cursor_sides := sides; cursor_spawns := spawns ++ [target];
    cursor_prefix := prefix_spawn Hprefix; cursor_watches := Hreads;
    cursor_raw := Hraw; cursor_ledger := Hledger |}.
  intros observed Hin; apply in_app_or in Hin; destruct Hin as [Hin |[<- |Hin]]; auto; contradiction.
Qed.

Lemma side_input_old fr target raw input : M.lookup (R.frame_local_side fr) target = Some input ->
  D.leq input (R.accumulated_side_input fr target raw) = true.
Proof. unfold R.accumulated_side_input; intro H; rewrite H; apply DL.join_upper_left. Qed.
Lemma side_input_raw fr target raw : D.leq raw (R.accumulated_side_input fr target raw) = true.
Proof. unfold R.accumulated_side_input; destruct (M.lookup (R.frame_local_side fr) target); auto using DL.leq_refl, DL.join_upper_right. Qed.
Lemma ledger_write st fr target raw next changed :
  R.write_side_contribution st (R.with_frame_side fr target (R.accumulated_side_input fr target raw))
    target (R.accumulated_side_input fr target raw) = (next,changed) ->
  side_ledger st fr -> side_ledger next (R.with_frame_side fr target (R.accumulated_side_input fr target raw)).
Proof.
  intros Hwrite Hledger observed input Hlookup; cbn [R.with_frame_side R.frame_local_side] in Hlookup.
  destruct (V.eq_dec observed target) as [-> |Hneq].
  - rewrite ML.lookup_update_same in Hlookup; inversion Hlookup; subst input; split.
    + cbn [R.with_frame_side R.frame_current_targets]; apply SL.add_spec; auto.
    + exact (write_contribution_sound Hwrite).
  - rewrite ML.lookup_update_other in Hlookup; auto; destruct (Hledger observed input Hlookup) as [Hmember Hbound]; split.
    + cbn [R.with_frame_side R.frame_current_targets]; apply SL.add_spec; auto.
    + cbn [R.with_frame_side R.frame_owner]; rewrite (write_other_contribution Hwrite (or_introl Hneq)); exact Hbound.
Qed.

Lemma cursor_side tf live st fr target raw tail next changed :
  R.write_side_contribution st (R.with_frame_side fr target (R.accumulated_side_input fr target raw))
    target (R.accumulated_side_input fr target raw) = (next,changed) ->
  cursor tf live st fr (Syntax.Side target raw tail) ->
  cursor tf live next (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) tail.
Proof.
  intros Hwrite [reads sides spawns Hprefix Hreads Hraw Hledger Hlive].
  pose proof (write_layout Hwrite) as [Hrank [Hqueue [Hsigma [Hreaders Htargets]]]].
  refine {| cursor_reads := reads; cursor_sides := sides ++ [(target,raw)]; cursor_spawns := spawns |}.
  - apply prefix_side; exact Hprefix.
  - eapply quiet_layout; [exact Hsigma |exact Hreaders |intros owner Hin; rewrite Hqueue; exact Hin |exact Hreads].
  - intros observed value Hin; apply in_app_or in Hin; destruct Hin as [Hin |[Heq |Hin]].
    + destruct (Hraw observed value Hin) as [input [Hlookup Hbound]].
      destruct (V.eq_dec observed target) as [-> |Hneq].
      * exists (R.accumulated_side_input fr target raw); split; [cbn; apply ML.lookup_update_same |].
        eapply DL.leq_trans; [exact Hbound |apply side_input_old; exact Hlookup].
      * exists input; split; [cbn; rewrite ML.lookup_update_other; auto |exact Hbound].
    + inversion Heq; subst observed value; exists (R.accumulated_side_input fr target raw); split;
        [cbn; apply ML.lookup_update_same |apply side_input_raw].
    + contradiction.
  - eapply ledger_write; eauto.
  - exact Hlive.
Qed.


Lemma cursor_dead tf live st fr target direct next changed :
  S.mem target (R.frame_current_targets fr) = false ->
  R.write_side_contribution st fr target D.bottom = (next,changed) ->
  cursor tf live st fr (Syntax.Ret direct) -> cursor tf live next fr (Syntax.Ret direct).
Proof.
  intros Habsent Hwrite [reads sides spawns Hprefix Hreads Hraw Hledger Hlive].
  pose proof (write_layout Hwrite) as [_ [Hq [Hs [Hr _]]]].
  refine {| cursor_reads := reads; cursor_sides := sides; cursor_spawns := spawns;
    cursor_prefix := Hprefix; cursor_raw := Hraw; cursor_live := Hlive |}.
  - eapply quiet_layout; [exact Hs |exact Hr |intros owner Hin; rewrite Hq; exact Hin |exact Hreads].
  - intros observed input Hlookup; destruct (Hledger observed input Hlookup) as [Hmember Hbound]; split; auto.
    rewrite (write_other_contribution Hwrite); [exact Hbound |].
    left; intro Heq; subst observed; congruence.
Qed.

Lemma cursor_evaluated tf live st fr direct :
  (forall target, live target -> solved st target) ->
  cursor tf live st fr (Syntax.Ret direct) -> evaluated_observation tf st (R.frame_owner fr) direct.
Proof.
  intros Hsolved [reads sides spawns Hprefix Hreads Hraw Hledger Hlive].
  refine {| evaluated_reads := reads; evaluated_sides := sides; evaluated_spawns := spawns;
    evaluated_trace := prefix_return Hprefix; evaluated_watches := Hreads |}.
  - intros target raw Hin; destruct (Hraw target raw Hin) as [input [Hlookup Hbound]].
    eapply DL.leq_trans; [exact Hbound |exact (proj2 (Hledger target input Hlookup))].
  - intros target Hin; apply Hsolved; apply Hlive; exact Hin.
Qed.

Definition live_reference c target := solved (R.cfg_state c) target \/ In target (active_owners (R.cfg_control c)).
Lemma live_reference_forward tf before after : frames_live before -> step tf before after ->
  forall target, live_reference before target -> live_reference after target.
Proof.
  intros Hframes Hstep target [Hsolved |Hactive]; unfold frames_live in Hframes.
  - left; eapply next_preserves_live; eauto.
  - destruct before as [st ctrl]; destruct ctrl;
      cbn [R.cfg_state R.cfg_control active_owners framed_owners frames_live] in Hframes, Hactive, Hstep.
    all: try contradiction.
    all: try solve [left; eapply next_preserves_live; [exact Hstep |rewrite Forall_forall in Hframes; apply Hframes; exact Hactive]].
    destruct Hactive as [<- |Hparent].
    + unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
        inversion Hstep; subst after; left; apply materialize_live.
    + left; eapply next_preserves_live; [exact Hstep |rewrite Forall_forall in Hframes; apply Hframes; exact Hparent].
Qed.
Lemma live_reference_solved c : frames_live c -> active_owners (R.cfg_control c) = framed_owners (R.cfg_control c) ->
  forall target, live_reference c target -> solved (R.cfg_state c) target.
Proof. intros Hframes Heq target [Hsolved |Hin]; unfold frames_live in Hframes; auto; rewrite Heq in Hin; rewrite Forall_forall in Hframes; apply Hframes; exact Hin. Qed.

Record guarded_observation tf (live : V.t -> Prop) st owner := {
  guarded_result : Sem.observation;
  guarded_trace : Sem.rhs_observes (tf owner) guarded_result;
  guarded_reads : quiet_reads st owner (Sem.observed_reads guarded_result);
  guarded_direct : D.leq (Sem.observed_direct guarded_result) (R.sigma_value st owner) = true;
  guarded_sides : forall target raw, In (target,raw) (Sem.observed_sides guarded_result) ->
    D.leq raw (R.stored_contribution st owner target) = true;
  guarded_spawns : forall target, In target (Sem.observed_spawns guarded_result) -> live target
}.
Lemma guarded_complete tf live st owner :
  (forall target, live target -> solved st target) -> ~ In owner (R.queue st) ->
  guarded_observation tf live st owner -> completed_observation tf st owner.
Proof.
  intros Hlive Hquiet [result Htrace Hreads Hdirect Hsides Hspawns].
  refine {| completed_result := result; completed_trace := Htrace;
    completed_reads := Hreads Hquiet; completed_direct := Hdirect; completed_sides := Hsides |}.
  intros target Hin; apply Hlive; apply Hspawns; exact Hin.
Qed.
Lemma guarded_transfer tf P Q st next owner :
  quiet_preserving st next -> R.sigma_value next owner = R.sigma_value st owner ->
  (forall target, R.stored_contribution next owner target = R.stored_contribution st owner target) ->
  (forall target, P target -> Q target) ->
  guarded_observation tf P st owner -> guarded_observation tf Q next owner.
Proof.
  intros Hw Hv Hs Hl [result Htrace Hreads Hdirect Hsides Hspawns].
  refine {| guarded_result := result; guarded_trace := Htrace |}.
  - apply Hw; exact Hreads.
  - rewrite Hv; exact Hdirect.
  - intros target raw Hin; rewrite Hs; apply Hsides; exact Hin.
  - intros target Hin; apply Hl; apply Hspawns; exact Hin.
Qed.

Lemma cursor_committed tf P Q st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) ->
  (forall target, P target -> Q target) -> cursor tf P st fr (Syntax.Ret direct) ->
  guarded_observation tf Q (R.requeue_changed_controlled_owner st next (R.frame_owner fr)) (R.frame_owner next_fr).
Proof.
  intros Hset Hlive [reads sides spawns Hprefix Hreads Hraw Hledger Hspawns].
  pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview.
  rewrite (commit_owner Hview).
  refine {| guarded_result :=
    {| Sem.Observation.observed_direct := direct; Sem.Observation.observed_reads := reads;
       Sem.Observation.observed_sides := sides; Sem.Observation.observed_spawns := spawns |};
    guarded_trace := prefix_return Hprefix |}.
  - eapply quiet_layout with (before := next); [reflexivity |reflexivity |apply requeue_keeps_queue |].
    apply (@quiet_set st fr direct next next_fr Hset); exact Hreads.
  - eapply DL.leq_trans; [apply DL.join_upper_left |exact (@commit_sound st fr direct next next_fr Hset)].
  - intros target raw Hin; cbn in Hin; destruct (Hraw target raw Hin) as [input [Hlookup Hbound]].
    unfold R.stored_contribution; cbn; rewrite (commit_contributions Hview).
    eapply DL.leq_trans; [exact Hbound |exact (proj2 (Hledger target input Hlookup))].
  - intros target Hin; apply Hlive; apply Hspawns; exact Hin.
Qed.

Fixpoint observing_stack tf live st k : Type :=
  match k with
  | R.KLoop | R.KSeedLoop _ => unit
  | R.KAfterGet fr target tail rest => (cursor tf live st fr (Syntax.Get target tail) * observing_stack tf live st rest)%type
  | R.KAfterSide fr tail rest |R.KAfterSpawn fr tail rest => (cursor tf live st fr tail * observing_stack tf live st rest)%type
  | R.KDead fr direct _ rest => (cursor tf live st fr (Syntax.Ret direct) * observing_stack tf live st rest)%type
  | R.KDrain fr rest => (guarded_observation tf live st (R.frame_owner fr) * observing_stack tf live st rest)%type
  end.
Definition observing_control tf c : Type :=
  let live := live_reference c in let st := R.cfg_state c in
  match R.cfg_control c return Type with
  | R.RunLoop |R.RunSeeds _ |R.RunSeedLoop _ => unit
  | R.StartEpisode _ k |R.Return k => observing_stack tf live st k
  | R.RunRhs fr body k => (cursor tf live st fr body * observing_stack tf live st k)%type
  | R.RunDead fr direct _ k |R.RunCommit fr direct k => (cursor tf live st fr (Syntax.Ret direct) * observing_stack tf live st k)%type
  | R.RunDrain fr k => (guarded_observation tf live st (R.frame_owner fr) * observing_stack tf live st k)%type
  end.
Lemma observing_stack_transfer tf P Q st next k :
  (forall fr body, In (R.frame_owner fr) (suspended_owners k) -> cursor tf P st fr body -> cursor tf Q next fr body) ->
  (forall owner, In owner (suspended_owners k) -> guarded_observation tf P st owner -> guarded_observation tf Q next owner) ->
  observing_stack tf P st k -> observing_stack tf Q next k.
Proof.
  intros Hcursor Hguarded Hstack; induction k; cbn [observing_stack suspended_owners] in *; try exact tt.
  all: destruct Hstack as [Hframe Hrest]; split.
  all: try solve [eapply Hcursor; [left; reflexivity |exact Hframe]].
  all: try solve [eapply Hguarded; [left; reflexivity |exact Hframe]].
  all: apply IHk; [intros fr body Hin H; apply Hcursor; [right; exact Hin |exact H]
    |intros owner Hin H; apply Hguarded; [right; exact Hin |exact H] |exact Hrest].
Qed.

Lemma cursor_same_frame tf P Q st next fr body : quiet_preserving st next ->
  (forall target, R.stored_contribution next (R.frame_owner fr) target = R.stored_contribution st (R.frame_owner fr) target) ->
  (forall target, P target -> Q target) -> cursor tf P st fr body -> cursor tf Q next fr body.
Proof. intros Hw Hs Hl H; eapply cursor_transfer; [reflexivity |reflexivity |reflexivity |exact (Hw (R.frame_owner fr)) |exact Hs |exact Hl |exact H]. Qed.
Lemma cursor_phase tf live st fr body phase : cursor tf live st fr body -> cursor tf live st (R.with_frame_phase fr phase) body.
Proof. intro H; eapply cursor_transfer with (st := st) (fr := fr) (P := live); [reflexivity |reflexivity |reflexivity |intros; assumption |intros; reflexivity |intros; assumption |exact H]. Qed.

Lemma aggregate_write_other st fr target input next changed observed :
  R.write_side_contribution st fr target input = (next,changed) -> observed <> target -> R.aggregate next observed = R.aggregate st observed.
Proof.
  unfold R.write_side_contribution; intros H Hneq; inversion H; subst next changed.
  unfold R.aggregate, R.register_reset, R.promote_side_target; cbn;
    destruct (R.rank_lt st target (R.frame_owner fr)); cbn; rewrite row_other; auto.
Qed.
Lemma aggregate_write_unchanged st fr target input next :
  R.write_side_contribution st fr target input = (next,false) -> eqv (R.aggregate next target) (R.aggregate st target).
Proof.
  unfold R.write_side_contribution; intro H; inversion H; subst next.
  unfold R.promote_side_target in *; destruct (R.rank_lt st target (R.frame_owner fr)); cbn in *.
  all: match goal with Hbool : negb _ = false |- _ => apply negb_false_iff in Hbool; apply eqv_bool; exact Hbool end.
Qed.

(** Transport is stated only for owners that retain their frames. A side
    write or commit belongs to the current owner; suspended owners are
    distinct and retain their own contribution rows and values. *)
Record frame_snapshot before after owners : Prop := {
  snapshot_reads : forall owner, In owner owners -> forall reads,
    quiet_reads before owner reads -> quiet_reads after owner reads;
  snapshot_values : forall owner, In owner owners -> R.sigma_value after owner = R.sigma_value before owner;
  snapshot_sides : forall owner, In owner owners -> forall target,
    R.stored_contribution after owner target = R.stored_contribution before owner target
}.
Arguments snapshot_reads {before after owners} _ {owner} _ reads _.
Arguments snapshot_values {before after owners} _ {owner} _.
Arguments snapshot_sides {before after owners} _ {owner} _ target.
Lemma snapshot_restrict before after xs ys :
  (forall owner, In owner xs -> In owner ys) -> frame_snapshot before after ys -> frame_snapshot before after xs.
Proof. intros Hsub [Hr Hv Hs]; constructor; intros; eauto. Qed.
Lemma snapshot_identity st owners : frame_snapshot st st owners.
Proof. constructor; intros; auto. Qed.
Lemma snapshot_compose before middle after owners : frame_snapshot before middle owners ->
  frame_snapshot middle after owners -> frame_snapshot before after owners.
Proof.
  intros [Hr1 Hv1 Hs1] [Hr2 Hv2 Hs2]; constructor; intros owner Hin.
  - intros reads H; apply Hr2; auto; apply Hr1; auto.
  - rewrite (Hv2 owner Hin), (Hv1 owner Hin); reflexivity.
  - intro target; rewrite (Hs2 owner Hin target), (Hs1 owner Hin target); reflexivity.
Qed.
Lemma snapshot_static before after owners : R.sigma after = R.sigma before -> R.readers after = R.readers before ->
  R.contributions after = R.contributions before ->
  (forall owner, In owner owners -> In owner (R.queue before) -> In owner (R.queue after)) -> frame_snapshot before after owners.
Proof.
  intros Hs Hr Hc Hq; constructor; intros owner Hin.
  - intros reads H Hquiet; eapply watched_layout; [exact Hs |exact Hr |apply H; intro Hqueued; apply Hquiet; apply Hq; auto].
  - unfold R.sigma_value; rewrite Hs; reflexivity.
  - intro target; unfold R.stored_contribution; rewrite Hc; reflexivity.
Qed.
Lemma materialize_sigma_value st target owner : R.sigma_value (R.materialize st target) owner = R.sigma_value st owner.
Proof.
  unfold R.materialize; destruct (M.lookup (R.sigma st) target) eqn:Ht; auto.
  unfold R.sigma_value; cbn; destruct (V.eq_dec owner target) as [-> |Hneq];
    [rewrite ML.lookup_update_same, Ht |rewrite ML.lookup_update_other]; auto.
Qed.
Lemma snapshot_materialize st target owners : frame_snapshot st (R.materialize st target) owners.
Proof.
  constructor; intros owner Hin.
  - apply quiet_materialize.
  - apply materialize_sigma_value.
  - intro observed; unfold R.materialize; destruct (M.lookup (R.sigma st) target); reflexivity.
Qed.
Lemma get_sigma_value st fr target next next_fr value owner : R.complete_get st fr target = (next,next_fr,value) ->
  R.sigma_value next owner = R.sigma_value st owner.
Proof.
  unfold R.complete_get; intro H; split_program H; rewrite materialize_sigma_value; reflexivity.
Qed.
Lemma snapshot_get st fr target next next_fr value owners : R.complete_get st fr target = (next,next_fr,value) -> frame_snapshot st next owners.
Proof.
  intro Hget; constructor; intros owner Hin.
  - apply (quiet_get Hget).
  - exact (get_sigma_value owner Hget).
  - intro observed; unfold R.stored_contribution; rewrite (proj1 (proj2 (proj2 (get_layout Hget)))); reflexivity.
Qed.
Lemma snapshot_side_write st fr target input next changed owners :
  R.write_side_contribution st fr target input = (next,changed) ->
  (forall owner, In owner owners -> owner <> R.frame_owner fr) -> frame_snapshot st next owners.
Proof.
  intros Hwrite Hother; pose proof (write_layout Hwrite) as [_ [Hq [Hs [Hr _]]]].
  constructor; intros owner Hin.
  - eapply quiet_layout; [exact Hs |exact Hr |intros x Hx; rewrite Hq; exact Hx].
  - unfold R.sigma_value; rewrite Hs; reflexivity.
  - intro observed; eapply write_other_contribution; [exact Hwrite |right; apply Hother; exact Hin].
Qed.
Lemma snapshot_commit st fr direct next next_fr owners : R.set_value st fr direct = (next,next_fr) ->
  (forall owner, In owner owners -> owner <> R.frame_owner fr) -> frame_snapshot st next owners.
Proof.
  intros Hset Hother; pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview.
  constructor; intros owner Hin.
  - apply (@quiet_set st fr direct next next_fr Hset).
  - unfold R.sigma_value; rewrite (commit_other Hview (Hother owner Hin)); reflexivity.
  - intro observed; unfold R.stored_contribution; rewrite (commit_contributions Hview); reflexivity.
Qed.
Lemma snapshot_pop st head rest owners : R.queue st = head :: rest ->
  (forall owner, In owner owners -> owner <> head) -> frame_snapshot st (R.with_queue st rest) owners.
Proof.
  intros Hq Hother; constructor; intros owner Hin; try reflexivity.
  intros reads H; eapply quiet_pop; [exact Hq |apply Hother; exact Hin |exact H].
Qed.

Lemma cursor_moved tf P Q st next fr body owners : frame_snapshot st next owners ->
  In (R.frame_owner fr) owners -> (forall target, P target -> Q target) ->
  cursor tf P st fr body -> cursor tf Q next fr body.
Proof.
  intros Hview Hin Hlive H; eapply cursor_transfer with (P := P) (st := st) (fr := fr);
    [reflexivity |reflexivity |reflexivity |exact (snapshot_reads Hview Hin)
    |exact (snapshot_sides Hview Hin) |exact Hlive |exact H].
Qed.
Lemma guarded_moved tf P Q st next owner owners : frame_snapshot st next owners -> In owner owners ->
  (forall target, P target -> Q target) -> guarded_observation tf P st owner -> guarded_observation tf Q next owner.
Proof.
  intros Hview Hin Hlive [result Htrace Hreads Hdirect Hsides Hspawns].
  refine {| guarded_result := result; guarded_trace := Htrace;
    guarded_reads := snapshot_reads Hview Hin _ Hreads |}.
  - rewrite (snapshot_values Hview Hin); exact Hdirect.
  - intros target raw Hraw; rewrite (snapshot_sides Hview Hin); apply Hsides; exact Hraw.
  - intros target Htarget; apply Hlive; apply Hspawns; exact Htarget.
Qed.
Lemma stack_moved tf P Q st next k : frame_snapshot st next (suspended_owners k) ->
  (forall target, P target -> Q target) -> observing_stack tf P st k -> observing_stack tf Q next k.
Proof.
  intros Hview Hlive H; apply observing_stack_transfer with (P := P) (st := st);
    [intros fr body Hin Hcursor; eapply cursor_moved; eauto
    |intros owner Hin Hguarded; eapply guarded_moved; eauto |exact H].
Qed.

Lemma parent_distinct (owner : V.t) parents : NoDup (owner :: parents) -> forall parent, In parent parents -> parent <> owner.
Proof. intros H parent Hin; inversion H; subst; congruence. Qed.
Lemma below_head order head rest owner : ordered order (head :: rest) ->
  head <> owner -> R.ranking_lt order owner head = false -> ~ In owner (head :: rest).
Proof.
  intros Hsorted Hneq Hlt [Heq |Hin]; [congruence |].
  destruct (ordered_tail Hsorted) as [_ Hall]; rewrite Forall_forall in Hall;
    pose proof (Hall owner Hin) as H; congruence.
Qed.

Lemma snapshot_observe st target owners : frame_snapshot st (R.observe st target) owners.
Proof. unfold R.observe; destruct (Ranks.observe (R.ranking st) target); apply snapshot_static; try reflexivity; auto. Qed.
Lemma snapshot_enqueue st target owners : frame_snapshot st (R.enqueue st target) owners.
Proof. apply snapshot_static; try reflexivity; intros owner Hin Hq; apply enqueue_members; auto. Qed.
Lemma snapshot_publish st fr owners : frame_snapshot st (R.publish_targets st fr) owners.
Proof. apply snapshot_static; try reflexivity; auto. Qed.
Lemma snapshot_close st owner owners : frame_snapshot st (R.reset_registered_cells st owner) owners.
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; apply snapshot_static; try reflexivity; auto. Qed.
Lemma snapshot_requeue before after owner owners : frame_snapshot after (R.requeue_changed_controlled_owner before after owner) owners.
Proof. apply snapshot_static; try reflexivity; intros; apply requeue_keeps_queue; assumption. Qed.
Lemma snapshot_tail st next owner parents : frame_snapshot st next (owner :: parents) -> frame_snapshot st next parents.
Proof. intro H; eapply snapshot_restrict with (ys := owner :: parents); [intros x Hin; right; exact Hin |exact H]. Qed.
Lemma child_distinct order owner parents child : ordered order (owner :: parents) ->
  R.ranking_lt order owner child = true -> forall parent, In parent (owner :: parents) -> parent <> child.
Proof.
  intros Hsorted Hlt parent [<- |Hin].
  - intro Heq; subst child; rewrite lt_irrefl in Hlt; discriminate.
  - destruct (ordered_tail Hsorted) as [_ Hall]; rewrite Forall_forall in Hall.
    intro Heq; subst child; pose proof (@lt_trans order parent owner parent (Hall parent Hin) Hlt) as H; rewrite lt_irrefl in H; discriminate.
Qed.
Ltac move_cursor Hview Hlive Hcursor :=
  eapply cursor_moved; [exact Hview |left; reflexivity |exact Hlive |exact Hcursor].
Ltac move_stack Hview Hlive Hstack :=
  eapply stack_moved; [exact Hview |exact Hlive |exact Hstack].
Ltac frame_from_full Hview Hlive Hcursor := move_cursor Hview Hlive Hcursor.
Ltac parents_from_full Hview Hlive Hstack :=
  eapply stack_moved; [eapply snapshot_tail; exact Hview |exact Hlive |exact Hstack].

Theorem next_observing_control tf before after : frames_live before -> active_ordered before ->
  inhabited (observing_control tf before) -> step tf before after -> inhabited (observing_control tf after).
Proof.
  intros Hframes Hordered [Hobserved] Hstep.
  pose proof (@live_reference_forward tf before after Hframes Hstep) as Hlive.
  pose proof (@ordered_unique (R.ranking (R.cfg_state before)) _ Hordered) as Hunique.
  destruct before as [st ctrl]; unfold observing_control in Hobserved |- *;
    destruct ctrl as [|roots|roots|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control active_owners active_ordered] in Hordered, Hunique, Hobserved, Hlive, Hstep |- *.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; try discriminate.
    inversion Hstep; subst after; constructor; exact tt.
  - destruct roots as [|root roots]; [inversion Hstep; subst after; constructor; exact tt |].
    destruct (R.is_materialized (R.observe st root) root); inversion Hstep; subst after; constructor; exact tt.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; inversion Hstep; subst after; constructor; exact tt.
  - inversion Hstep; subst after; constructor; split; [apply cursor_fresh |].
    move_stack (snapshot_materialize st owner (suspended_owners k)) Hlive Hobserved.
  - destruct Hobserved as [Hcursor Hstack]; destruct body as [direct |target tail |target raw tail |target tail].
    + inversion Hstep; subst after; constructor; split.
      * frame_from_full (snapshot_identity st (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor.
      * move_stack (snapshot_identity st (suspended_owners k)) Hlive Hstack.
    + destruct (negb (R.is_materialized (R.observe st target) target) &&
        R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
      * inversion Hstep; subst after; constructor; split.
        -- frame_from_full (snapshot_observe st target (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor.
        -- move_stack (snapshot_observe st target (suspended_owners k)) Hlive Hstack.
      * set (st0 := if R.is_materialized (R.observe st target) target then R.observe st target
          else R.enqueue (R.observe st target) target) in *.
        assert (H0 : frame_snapshot st st0 (R.frame_owner fr :: suspended_owners k)).
        { unfold st0; destruct (R.is_materialized (R.observe st target) target);
            [apply snapshot_observe |eapply snapshot_compose; [apply snapshot_observe |apply snapshot_enqueue]]. }
        destruct (R.complete_get st0 fr target) as [[done next_fr] value] eqn:Hget.
        inversion Hstep; subst after; constructor; split.
        -- eapply cursor_get; [exact Hget |frame_from_full H0 Hlive Hcursor].
        -- parents_from_full (@snapshot_compose st st0 done _ H0 (snapshot_get _ Hget)) Hlive Hstack.
    + unfold R.record_side_input in Hstep.
      set (input := R.accumulated_side_input fr target raw) in *.
      destruct (R.write_side_contribution (R.observe st target) (R.with_frame_side fr target input) target input)
        as [done changed] eqn:Hwrite.
      assert (Hparents : frame_snapshot st done (suspended_owners k)).
      { eapply snapshot_compose; [apply snapshot_observe |eapply snapshot_side_write; [exact Hwrite |]].
        cbn [R.with_frame_side R.frame_owner]; apply parent_distinct; exact Hunique. }
      assert (Hframe : cursor tf (live_reference after) done (R.with_frame_side fr target input) tail).
      { eapply cursor_side; [exact Hwrite |].
        frame_from_full (snapshot_observe st target (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor. }
      unfold R.continue_side in Hstep; destruct changed;
        [destruct (R.rank_lt done (R.frame_owner (R.with_frame_side fr target input)) target && negb (R.is_materialized done target))%bool |];
        inversion Hstep; subst after; constructor; split.
      all: try exact Hframe.
      all: try solve [move_stack Hparents Hlive Hstack].
      * eapply cursor_moved; [exact (snapshot_enqueue done target (R.frame_owner fr :: suspended_owners k))
          |left; reflexivity |intros x H; exact H |exact Hframe].
      * move_stack (@snapshot_compose st done (R.enqueue done target) _ Hparents (snapshot_enqueue _ _ _)) Hlive Hstack.
    + destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
      * inversion Hstep; subst after; constructor; split.
        -- apply cursor_spawn with (target := target).
           ++ left; apply materialized_solved; exact Hmat.
           ++ frame_from_full (snapshot_observe st target (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor.
        -- move_stack (snapshot_observe st target (suspended_owners k)) Hlive Hstack.
      * destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target).
        -- inversion Hstep; subst after; constructor; split.
           ++ apply cursor_spawn with (target := target); [right; left; reflexivity |].
              frame_from_full (snapshot_observe st target (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor.
           ++ move_stack (snapshot_observe st target (suspended_owners k)) Hlive Hstack.
        -- inversion Hstep; subst after; constructor; split.
           ++ apply cursor_spawn with (target := target); [left; apply materialize_live |].
              eapply cursor_moved with (owners := R.frame_owner fr :: suspended_owners k); [|left; reflexivity |exact Hlive |exact Hcursor].
              eapply snapshot_compose; [apply snapshot_observe |].
              eapply snapshot_compose; [apply snapshot_enqueue |apply snapshot_materialize].
           ++ eapply stack_moved; [|exact Hlive |exact Hstack].
              eapply snapshot_compose; [apply snapshot_observe |].
              eapply snapshot_compose; [apply snapshot_enqueue |apply snapshot_materialize].
  - destruct Hobserved as [Hcursor Hstack]; destruct pending as [|target pending].
    + inversion Hstep; subst after; constructor; split.
      * frame_from_full (snapshot_publish st fr (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor.
      * move_stack (snapshot_publish st fr (suspended_owners k)) Hlive Hstack.
    + destruct (S.mem target (R.frame_current_targets fr)) eqn:Hcurrent.
      * inversion Hstep; subst after; constructor; split.
        -- frame_from_full (snapshot_identity st (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor.
        -- move_stack (snapshot_identity st (suspended_owners k)) Hlive Hstack.
      * destruct (R.write_side_contribution st fr target D.bottom) as [done changed] eqn:Hwrite.
        assert (Hparents : frame_snapshot st done (suspended_owners k)) by
          (eapply snapshot_side_write; [exact Hwrite |apply parent_distinct; exact Hunique]).
        assert (Hframe : cursor tf (live_reference after) done fr (Syntax.Ret direct)).
        { eapply cursor_dead; [exact Hcurrent |exact Hwrite |].
          frame_from_full (snapshot_identity st (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor. }
        unfold R.continue_dead in Hstep; destruct changed;
          [destruct (R.rank_lt done (R.frame_owner fr) target && negb (R.is_materialized done target))%bool |];
          inversion Hstep; subst after; constructor; split.
        all: try exact Hframe.
        all: try solve [move_stack Hparents Hlive Hstack].
        -- eapply cursor_moved; [exact (snapshot_enqueue done target (R.frame_owner fr :: suspended_owners k))
          |left; reflexivity |intros x H; exact H |exact Hframe].
        -- move_stack (@snapshot_compose st done (R.enqueue done target) _ Hparents (snapshot_enqueue _ _ _)) Hlive Hstack.
  - destruct Hobserved as [Hcursor Hstack]; destruct (R.set_value st fr direct) as [done next_fr] eqn:Hset.
    inversion Hstep; subst after; constructor; split.
    + eapply cursor_committed; [exact Hset |exact Hlive |exact Hcursor].
    + eapply stack_moved; [|exact Hlive |exact Hstack].
      eapply snapshot_compose; [eapply snapshot_commit; [exact Hset |apply parent_distinct; exact Hunique] |apply snapshot_requeue].
  - destruct Hobserved as [Hguarded Hstack]; destruct (R.queue_peek (R.queue st)) as [next|] eqn:Hpeek.
    + destruct (V.eq_dec next (R.frame_owner fr)) as [Heq |Hneq].
      * destruct (R.queue_pop (R.queue st)) as [[head rest]|] eqn:Hpop; try discriminate.
        assert (Hhead : head = next) by (pose proof (@peek_popped (R.queue st) head rest Hpop); congruence); subst head next.
        inversion Hstep; subst after; constructor; split; [apply cursor_fresh |].
        eapply stack_moved; [|exact Hlive |exact Hstack]; eapply snapshot_pop.
        -- unfold R.queue_pop in Hpop; destruct (R.queue st); inversion Hpop; reflexivity.
        -- apply parent_distinct; exact Hunique.
      * destruct (R.rank_lt st (R.frame_owner fr) next) eqn:Hlt.
        -- destruct (R.queue_pop (R.queue st)) as [[head rest]|] eqn:Hpop; try discriminate.
           assert (Hhead : head = next) by (pose proof (@peek_popped (R.queue st) head rest Hpop); congruence); subst head.
           assert (Hview : frame_snapshot st (R.with_queue st rest) (R.frame_owner fr :: suspended_owners k)).
           { eapply snapshot_pop.
             - unfold R.queue_pop in Hpop; destruct (R.queue st); inversion Hpop; reflexivity.
             - apply child_distinct with (order := R.ranking st); [exact Hordered |exact Hlt]. }
           inversion Hstep; subst after; constructor; split.
           ++ eapply guarded_moved; [exact Hview |left; reflexivity |exact Hlive |exact Hguarded].
           ++ parents_from_full Hview Hlive Hstack.
        -- inversion Hstep; subst after; constructor;
           move_stack (snapshot_close st (R.frame_owner fr) (suspended_owners k)) Hlive Hstack.
    + inversion Hstep; subst after; constructor;
      move_stack (snapshot_close st (R.frame_owner fr) (suspended_owners k)) Hlive Hstack.
  - destruct k as [|roots|fr target tail k|fr tail k|fr tail k|fr direct pending k|fr k]; cbn [observing_stack] in Hobserved.
    + inversion Hstep; subst after; constructor; exact tt.
    + inversion Hstep; subst after; constructor; exact tt.
    + destruct Hobserved as [Hcursor Hstack]; destruct (R.complete_get st fr target) as [[done next_fr] value] eqn:Hget.
      inversion Hstep; subst after; constructor; split.
      * eapply cursor_get; [exact Hget |frame_from_full (snapshot_identity st (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor].
      * move_stack (snapshot_get (suspended_owners k) Hget) Hlive Hstack.
    + destruct Hobserved as [Hcursor Hstack]; inversion Hstep; subst after; constructor; split.
      * frame_from_full (snapshot_identity st (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor.
      * move_stack (snapshot_identity st (suspended_owners k)) Hlive Hstack.
    + destruct Hobserved as [Hcursor Hstack]; inversion Hstep; subst after; constructor; split.
      * frame_from_full (snapshot_identity st (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor.
      * move_stack (snapshot_identity st (suspended_owners k)) Hlive Hstack.
    + destruct Hobserved as [Hcursor Hstack]; inversion Hstep; subst after; constructor; split.
      * frame_from_full (snapshot_identity st (R.frame_owner fr :: suspended_owners k)) Hlive Hcursor.
      * move_stack (snapshot_identity st (suspended_owners k)) Hlive Hstack.
    + destruct Hobserved as [Hguarded Hstack]; inversion Hstep; subst after; constructor; split.
      * eapply guarded_moved; [apply snapshot_identity with (owners := R.frame_owner fr :: suspended_owners k) |left; reflexivity |exact Hlive |exact Hguarded].
      * move_stack (snapshot_identity st (suspended_owners k)) Hlive Hstack.
Qed.

Fixpoint waiting_stack (P : V.t -> Prop) k : Prop :=
  match k with
  | R.KLoop |R.KSeedLoop _ => True
  | R.KAfterGet _ target _ rest => P target /\ waiting_stack P rest
  | R.KAfterSide _ _ rest |R.KAfterSpawn _ _ rest |R.KDead _ _ _ rest |R.KDrain _ rest => waiting_stack P rest
  end.
Definition waiting_control c :=
  match R.cfg_control c with
  | R.RunLoop |R.RunSeeds _ |R.RunSeedLoop _ => True
  | R.StartEpisode _ k |R.RunRhs _ _ k |R.RunDead _ _ _ k |R.RunCommit _ _ k |R.RunDrain _ k |R.Return k =>
    waiting_stack (live_reference c) k
  end.
Lemma waiting_lift P Q k : (forall x, P x -> Q x) -> waiting_stack P k -> waiting_stack Q k.
Proof. intro Hlift; induction k; cbn [waiting_stack]; intuition auto. Qed.
Lemma next_waiting_control tf before after : frames_live before -> waiting_control before ->
  step tf before after -> waiting_control after.
Proof.
  intros Hframes Hwaiting Hstep; pose proof (@live_reference_forward tf before after Hframes Hstep) as Hlift.
  destruct before as [st ctrl]; unfold waiting_control in Hwaiting |- *;
    unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [R.cfg_control] in Hstep, Hwaiting;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep.
  all: cbn [R.cfg_state R.cfg_control waiting_stack] in Hwaiting |- *;
    try exact I; try solve [eapply waiting_lift; [exact Hlift |exact Hwaiting]].
  - split; [right; left; reflexivity |eapply waiting_lift; [exact Hlift |exact Hwaiting]].
  - destruct Hwaiting as [Htarget Hrest]; eapply waiting_lift; [exact Hlift |exact Hrest].
Qed.

Definition idle c owner := ~ In owner (R.queue (R.cfg_state c)) /\ ~ In owner (active_owners (R.cfg_control c)).
Definition closing before after owner := exists fr k,
  R.cfg_control before = R.RunDrain fr k /\ R.cfg_control after = R.Return k /\ owner = R.frame_owner fr.
Lemma next_active_origin tf before after : step tf before after -> forall owner,
  In owner (active_owners (R.cfg_control before)) ->
  In owner (active_owners (R.cfg_control after)) \/ closing before after owner.
Proof.
  intro Hstep; destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep; primitive_views.
  all: cbn [R.cfg_state R.cfg_control active_owners suspended_owners R.frame_owner R.fresh_frame R.with_frame_side] in *;
    repeat match goal with Ho : R.frame_owner _ = R.frame_owner _ |- _ => rewrite Ho in *; clear Ho end;
    intros owner Hin; try solve [left; cbn; intuition auto].
  all: destruct Hin as [<- |Hin]; [right; eexists; eexists; repeat split; reflexivity |left; exact Hin].
Qed.
Lemma next_idle_origin tf before after : step tf before after -> forall owner,
  idle after owner -> idle before owner \/ closing before after owner.
Proof.
  intros Hstep owner [Hq Ha].
  assert (Hbeforeq : ~ In owner (R.queue (R.cfg_state before))).
  { intro Hin; destruct (@next_queue_covered tf before after Hstep owner Hin); contradiction. }
  destruct (in_dec V.eq_dec owner (active_owners (R.cfg_control before))) as [Hin |Hnot].
  - destruct (@next_active_origin tf before after Hstep owner Hin) as [Hafter |Hclosed]; [contradiction |auto].
  - left; split; assumption.
Qed.
Lemma solved_materialize_back st target owner : solved (R.materialize st target) owner -> solved st owner \/ owner = target.
Proof.
  unfold R.materialize; destruct (M.lookup (R.sigma st) target) eqn:Ht; auto.
  intros [value Hv]; change (M.lookup (M.update (R.sigma st) target D.bottom) owner = Some value) in Hv.
  destruct (V.eq_dec owner target) as [Heq |Hneq]; auto; left; exists value; rewrite ML.lookup_update_other in Hv; auto.
Qed.
Lemma solved_get_back st fr target next next_fr value owner : R.complete_get st fr target = (next,next_fr,value) ->
  solved next owner -> solved st owner \/ owner = target.
Proof.
  unfold R.complete_get; intro H; split_program H.
  all: intro Hlive; apply solved_materialize_back in Hlive; destruct Hlive as [Hlive |Heq]; [left; exact Hlive |auto].
Qed.
Lemma solved_commit_back st fr direct next next_fr owner : R.set_value st fr direct = (next,next_fr) ->
  solved st (R.frame_owner fr) -> solved next owner -> solved st owner.
Proof.
  intros Hset Howner [value Hvalue]; pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview.
  destruct (V.eq_dec owner (R.frame_owner fr)) as [-> |Hneq]; auto.
  exists value; change (M.lookup (R.sigma next) owner = Some value) in Hvalue;
    rewrite (commit_other Hview Hneq) in Hvalue; exact Hvalue.
Qed.
Lemma solved_layout_back before after : R.sigma after = R.sigma before -> forall owner, solved after owner -> solved before owner.
Proof. intros H owner [value Hv]; exists value; change (M.lookup (R.sigma after) owner = Some value) in Hv; rewrite H in Hv; exact Hv. Qed.

Fixpoint drained_stack k : list V.t :=
  match k with
  | R.KLoop |R.KSeedLoop _ => []
  | R.KDrain fr rest => R.frame_owner fr :: drained_stack rest
  | R.KAfterGet _ _ _ rest |R.KAfterSide _ _ rest |R.KAfterSpawn _ _ rest |R.KDead _ _ _ rest => drained_stack rest
  end.
Definition drained_owners ctrl :=
  match ctrl with
  | R.RunLoop |R.RunSeeds _ |R.RunSeedLoop _ => []
  | R.RunDrain fr k => R.frame_owner fr :: drained_stack k
  | R.StartEpisode _ k |R.RunRhs _ _ k |R.RunDead _ _ _ k |R.RunCommit _ _ k |R.Return k => drained_stack k
  end.
Definition incoming_ready c owner := ~ In owner (R.queue (R.cfg_state c)) /\
  (~ In owner (active_owners (R.cfg_control c)) \/ In owner (drained_owners (R.cfg_control c))).
Definition incoming_safe c := forall owner, incoming_ready c owner ->
  D.leq (R.aggregate (R.cfg_state c) owner) (R.sigma_value (R.cfg_state c) owner) = true.
Definition committing before owner := exists fr direct k,
  R.cfg_control before = R.RunCommit fr direct k /\ owner = R.frame_owner fr.
Lemma drained_parent k owner : In owner (drained_stack k) -> In owner (suspended_owners k).
Proof. induction k; cbn [drained_stack suspended_owners]; cbn; intuition auto. Qed.
Lemma next_drained_origin tf before after : step tf before after -> forall owner,
  In owner (drained_owners (R.cfg_control after)) ->
  In owner (drained_owners (R.cfg_control before)) \/ committing before owner.
Proof.
  intro Hstep; destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep; primitive_views.
  all: cbn [R.cfg_state R.cfg_control drained_owners drained_stack R.frame_owner R.fresh_frame R.with_frame_side] in *;
    repeat match goal with Ho : R.frame_owner _ = R.frame_owner _ |- _ => rewrite Ho in *; clear Ho end;
    intros owner Hin; try solve [left; cbn; intuition auto].
  destruct Hin as [<- |Hin]; [right; eexists; eexists; eexists; split; reflexivity |left; exact Hin].
Qed.

Lemma next_drained_wakeup tf before after : NoDup (active_owners (R.cfg_control after)) ->
  step tf before after -> forall owner, In owner (R.queue (R.cfg_state before)) ->
  In owner (drained_owners (R.cfg_control after)) -> In owner (R.queue (R.cfg_state after)).
Proof.
  intros Hunique Hstep; destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep.
  all: cbn [R.cfg_state R.cfg_control active_owners drained_owners drained_stack
      R.frame_owner R.fresh_frame R.with_frame_side R.with_queue R.queue R.enqueue] in Hunique |- *;
    intros owner Hqueue Hdrained; try contradiction.
  all: try solve [exact Hqueue |apply insert_members; auto |apply requeue_keeps_queue; eapply commit_keeps_queue; eauto].
  all: repeat first [rewrite close_queue |rewrite observe_queue |rewrite materialize_queue
    |match goal with Hget : R.complete_get _ _ _ = (_,_,_) |- _ => rewrite (get_queue Hget); clear Hget end
    |match goal with Hwrite : R.write_side_contribution _ _ _ _ = (_,_) |- _ => rewrite (write_queue Hwrite); clear Hwrite end
    |progress cbn [R.enqueue R.with_queue R.queue]];
    try solve [exact Hqueue |apply insert_members; auto].
  all: try solve [match goal with |- context [if ?b then _ else _] => destruct b; cbn; rewrite ?observe_queue; [exact Hqueue |apply insert_members; auto] end].
  all: repeat match goal with Hpeek : R.queue_peek ?q = Some ?x, Hpop : R.queue_pop ?q = Some (?head,?rest) |- _ =>
    assert (head = x) by (pose proof (@peek_popped q head rest Hpop); congruence); subst head; clear Hpeek end.
  all: match goal with Hpop : R.queue_pop ?q = Some (?head,?rest) |- _ =>
    destruct (@popped_members q head rest owner Hpop Hqueue) as [Heq |Hin]; [subst owner |exact Hin] end.
  all: inversion Hunique; subst; exfalso; match goal with Hnot : ~ In _ _ |- _ => apply Hnot end.
  all: try solve [apply drained_parent; exact Hdrained].
  cbn; destruct Hdrained as [Heq |Hin]; [left; exact Heq |right; apply drained_parent; exact Hin].
Qed.
Lemma next_incoming_origin tf before after : NoDup (active_owners (R.cfg_control after)) -> step tf before after -> forall owner,
  incoming_ready after owner -> incoming_ready before owner \/ committing before owner.
Proof.
  intros Hunique Hstep owner [Hquiet [Hidle |Hdrained]].
  - destruct (@next_idle_origin tf before after Hstep owner (conj Hquiet Hidle)) as [[Hq Ha] |[fr [k [Hbefore [Hafter ->]]]]].
    + left; split; auto.
    + left; split.
      * intro Hin; destruct (@next_queue_covered tf before after Hstep (R.frame_owner fr) Hin) as [Hq |Ha]; [contradiction |apply Hidle; exact Ha].
      * right; rewrite Hbefore; left; reflexivity.
  - destruct (@next_drained_origin tf before after Hstep owner Hdrained) as [Hbefore |Hcommit]; [left |auto].
    split; [|right; exact Hbefore].
    intro Hin; apply Hquiet; eapply next_drained_wakeup; eauto.
Qed.

Lemma observe_sigma st target : R.sigma (R.observe st target) = R.sigma st.
Proof. unfold R.observe; destruct (Ranks.observe (R.ranking st) target); reflexivity. Qed.
Ltac old_solved H :=
  match type of H with solved ?next ?owner =>
    eapply solved_layout_back with (after := next); [cbn [R.enqueue R.with_queue R.sigma]; rewrite ?observe_sigma; reflexivity |exact H] end.
Lemma next_solved_origin tf before after : frames_live before -> waiting_control before -> step tf before after ->
  forall owner, solved (R.cfg_state after) owner -> solved (R.cfg_state before) owner \/
    In owner (R.queue (R.cfg_state after)) \/ In owner (active_owners (R.cfg_control after)).
Proof.
  intros Hframes Hwaiting Hstep; destruct before as [st ctrl];
    unfold frames_live in Hframes; unfold waiting_control in Hwaiting; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [R.cfg_control framed_owners active_owners] in Hstep, Hframes, Hwaiting;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep.
  all: cbn [R.cfg_state R.cfg_control active_owners suspended_owners R.frame_owner R.fresh_frame R.with_frame_side] in *.
  all: try solve [intros owner H; left; exact H].
  all: try solve [intros owner H; left; old_solved H].
  all: try solve [intros owner H; apply solved_materialize_back in H; destruct H as [H | ->]; [left; exact H |right; right; left; reflexivity]].
  all: try solve [intros owner H; apply solved_materialize_back in H; destruct H as [H | ->]; [left; old_solved H |right; left; rewrite materialize_queue; apply enqueue_members; auto]].
  all: try solve [intros owner H; left; unfold R.reset_registered_cells in H; destruct Features.restart_side_phases; exact H].
  all: try match goal with Hwrite : R.write_side_contribution _ _ _ _ = (_,_) |- _ =>
    pose proof (write_layout Hwrite) as [_ [_ [Hs _]]]; intros owner H; left; eapply solved_layout_back; [rewrite Hs, ?observe_sigma; reflexivity |exact H] end.
  all: try match goal with Hset : R.set_value _ ?fr _ = (_,_) |- _ =>
    intros owner H; left; eapply solved_commit_back; [exact Hset |rewrite Forall_forall in Hframes; apply Hframes; left; reflexivity |exact H] end.
  all: try match goal with Hget : context [if ?b then _ else _] |- _ => destruct b eqn:Hmaterialized end.
  all: match goal with Hget : R.complete_get ?input ?fr ?target = (_,_,_) |- _ =>
    intros owner H; destruct (solved_get_back Hget H) as [Hbefore |Heq];
      [left; old_solved Hbefore |subst owner] end.
  all: try solve [left; match goal with Hmat : R.is_materialized ?state ?x = true |- _ =>
    let Hknown := fresh "known_target" in pose proof (@materialized_solved state x Hmat) as Hknown; old_solved Hknown end].
  all: try solve [right; left; rewrite (get_queue ltac:(eassumption)); apply enqueue_members; auto].
  cbn [waiting_stack] in Hwaiting; destruct Hwaiting as [Htarget _]; left;
    match type of Htarget with live_reference ?config ?target =>
      exact (@live_reference_solved config Hframes eq_refl target Htarget) end.
Qed.

Definition settled_store tf c := forall owner, solved (R.cfg_state c) owner -> idle c owner ->
  inhabited (completed_observation tf (R.cfg_state c) owner).
Lemma completed_guarded tf st owner (done : completed_observation tf st owner) : guarded_observation tf (solved st) st owner.
Proof.
  destruct done as [result Htrace Hreads Hdirect Hsides Hspawns].
  refine {| guarded_result := result; guarded_trace := Htrace; guarded_direct := Hdirect;
    guarded_sides := Hsides; guarded_spawns := Hspawns |}; intros _; exact Hreads.
Qed.
Lemma completed_moved tf before after owner : frame_snapshot (R.cfg_state before) (R.cfg_state after) [owner] ->
  preserves_live (R.cfg_state before) (R.cfg_state after) -> ~ In owner (R.queue (R.cfg_state after)) ->
  completed_observation tf (R.cfg_state before) owner -> completed_observation tf (R.cfg_state after) owner.
Proof.
  intros Hview Hlive Hquiet Hdone; eapply guarded_complete with (live := solved (R.cfg_state after)); [auto |exact Hquiet |].
  eapply guarded_moved; [exact Hview |left; reflexivity |exact Hlive |apply completed_guarded; exact Hdone].
Qed.

Lemma next_idle_snapshot tf before after owner : step tf before after -> idle before owner -> idle after owner ->
  frame_snapshot (R.cfg_state before) (R.cfg_state after) [owner].
Proof.
  intros Hstep [Hqbefore Habefore] [Hqafter Haafter].
  destruct before as [st ctrl]; unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [R.cfg_control active_owners] in Habefore, Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep.
  all: cbn [R.cfg_state R.cfg_control] in *.
  all: try solve [apply snapshot_identity |apply snapshot_observe |apply snapshot_publish |apply snapshot_close].
  all: try solve [apply snapshot_static; try reflexivity; intros x [<- |Hfalse] Hq; [exfalso; apply Hqbefore; exact Hq |contradiction]].
  all: try solve [apply snapshot_materialize].
  all: try match goal with Hget : R.complete_get ?input _ _ = (_,_,_) |- _ =>
    eapply snapshot_compose; [|apply (snapshot_get [owner] Hget)];
    try solve [apply snapshot_identity |apply snapshot_observe |
      eapply snapshot_compose; [apply snapshot_observe |apply snapshot_enqueue]] end.
  all: try match goal with Hwrite : R.write_side_contribution ?input ?fr _ _ = (?next,_) |- _ =>
    assert (Hother : forall x, In x [owner] -> x <> R.frame_owner fr) by
      (intros x [<- |Hfalse]; [intro Heq; apply Habefore; cbn; left; symmetry; exact Heq |contradiction]);
    try solve [eapply snapshot_side_write; eauto |
      eapply snapshot_compose; [apply snapshot_observe |eapply snapshot_side_write; eauto] |
      eapply snapshot_compose with (middle := next); [|apply snapshot_enqueue];
        try solve [eapply snapshot_side_write; eauto |
          eapply snapshot_compose; [apply snapshot_observe |eapply snapshot_side_write; eauto]]] end.
  all: try match goal with Hset : R.set_value ?input ?fr _ = (?next,_) |- _ =>
    eapply snapshot_compose; [eapply snapshot_commit; [exact Hset |intros x [<- |Hfalse];
      [intro Heq; apply Habefore; left; symmetry; exact Heq |contradiction]] |apply snapshot_requeue] end.
  all: try solve [eapply snapshot_compose; [apply snapshot_observe |];
    eapply snapshot_compose; [apply snapshot_enqueue |apply snapshot_materialize]].
  match goal with |- context [if ?b then _ else _] => destruct b end;
    [apply snapshot_observe |eapply snapshot_compose; [apply snapshot_observe |apply snapshot_enqueue]].
Qed.

Lemma aggregate_observe st target owner : R.aggregate (R.observe st target) owner = R.aggregate st owner.
Proof. unfold R.observe; destruct (Ranks.observe (R.ranking st) target); reflexivity. Qed.
Lemma value_observe st target owner : R.sigma_value (R.observe st target) owner = R.sigma_value st owner.
Proof. unfold R.sigma_value; rewrite observe_sigma; reflexivity. Qed.
Lemma aggregate_materialize st target owner : R.aggregate (R.materialize st target) owner = R.aggregate st owner.
Proof. unfold R.materialize; destruct (M.lookup (R.sigma st) target); reflexivity. Qed.
Lemma aggregate_get st fr target next next_fr value owner : R.complete_get st fr target = (next,next_fr,value) ->
  R.aggregate next owner = R.aggregate st owner.
Proof. intro H; unfold R.aggregate; rewrite (proj1 (proj2 (proj2 (get_layout H)))); reflexivity. Qed.
Lemma write_preserves_incoming st fr target input next changed owner :
  R.write_side_contribution st fr target input = (next,changed) ->
  D.leq (R.aggregate st owner) (R.sigma_value st owner) = true ->
  (changed = true -> owner <> target) -> D.leq (R.aggregate next owner) (R.sigma_value next owner) = true.
Proof.
  intros Hwrite Hbound Hother; pose proof (write_layout Hwrite) as [_ [_ [Hs _]]].
  assert (Hv : R.sigma_value next owner = R.sigma_value st owner) by (unfold R.sigma_value; rewrite Hs; reflexivity).
  rewrite Hv; destruct (V.eq_dec owner target) as [-> |Hneq].
  - destruct changed; [exfalso; apply (Hother eq_refl); reflexivity |].
    eapply DL.leq_trans; [exact (proj1 (aggregate_write_unchanged Hwrite)) |exact Hbound].
  - rewrite (aggregate_write_other Hwrite Hneq); exact Hbound.
Qed.
Lemma starting_not_ready st target k owner : NoDup (target :: suspended_owners k) ->
  incoming_ready {| R.cfg_state := st; R.cfg_control := R.StartEpisode target k |} owner -> owner <> target.
Proof.
  intros Hunique [_ [Hnot |Hdrained]] Heq; subst owner.
  - apply Hnot; left; reflexivity.
  - inversion Hunique; subst; apply H1; apply drained_parent; exact Hdrained.
Qed.

Lemma aggregate_enqueue st target owner : R.aggregate (R.enqueue st target) owner = R.aggregate st owner.
Proof. reflexivity. Qed.
Lemma value_enqueue st target owner : R.sigma_value (R.enqueue st target) owner = R.sigma_value st owner.
Proof. reflexivity. Qed.
Lemma next_incoming_bound tf before after owner : NoDup (active_owners (R.cfg_control after)) ->
  step tf before after -> incoming_ready after owner ->
  D.leq (R.aggregate (R.cfg_state before) owner) (R.sigma_value (R.cfg_state before) owner) = true ->
  D.leq (R.aggregate (R.cfg_state after) owner) (R.sigma_value (R.cfg_state after) owner) = true.
Proof.
  intros Hunique Hstep Hready Hbound; destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep, Hbound.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep.
  all: cbn [R.cfg_state R.cfg_control active_owners suspended_owners R.frame_owner R.fresh_frame R.with_frame_side] in Hunique |- *.
  all: try solve [exact Hbound].
  all: try solve [rewrite ?aggregate_materialize, ?materialize_sigma_value, ?aggregate_enqueue, ?value_enqueue, ?aggregate_observe, ?value_observe; exact Hbound].
  all: try solve [unfold R.reset_registered_cells; destruct Features.restart_side_phases; exact Hbound].
  all: try match goal with Hget : R.complete_get _ _ _ = (_,_,_) |- _ =>
    rewrite (aggregate_get owner Hget), (get_sigma_value owner Hget);
    try solve [rewrite ?aggregate_enqueue, ?value_enqueue, ?aggregate_observe, ?value_observe; exact Hbound] end.
  all: try match goal with Hset : R.set_value ?input ?fr ?direct = (?next,?next_fr) |- _ =>
    change (D.leq (R.aggregate next owner) (R.sigma_value next owner) = true);
    pose proof (@commit_footprint input fr direct next next_fr Hset) as Hview;
    destruct (V.eq_dec owner (R.frame_owner fr)) as [Heq |Hneq];
    [subst owner; unfold R.aggregate; rewrite (commit_contributions Hview);
      eapply DL.leq_trans; [apply DL.join_upper_right |exact (@commit_sound input fr direct next next_fr Hset)]
    |unfold R.aggregate, R.sigma_value; rewrite (commit_contributions Hview), (commit_other Hview Hneq); exact Hbound] end.
  all: try match goal with Hwrite : R.write_side_contribution ?input ?fr ?target _ = (?next,?changed) |- _ =>
    change (D.leq (R.aggregate next owner) (R.sigma_value next owner) = true);
    eapply write_preserves_incoming; [exact Hwrite |rewrite ?aggregate_enqueue, ?value_enqueue, ?aggregate_observe, ?value_observe; exact Hbound |] end.
  all: try solve [discriminate].
  all: try solve [intros _ Heq; subst owner; apply (proj1 Hready); apply enqueue_members; auto].
  all: try solve [intros _; eapply starting_not_ready; [exact Hunique |exact Hready]].
  match goal with |- context [if ?b then _ else _] => destruct b end;
    rewrite ?aggregate_enqueue, ?value_enqueue, ?aggregate_observe, ?value_observe; exact Hbound.
  all: intros _; match type of Hready with
    incoming_ready {| R.cfg_state := ?state; R.cfg_control := R.StartEpisode ?target ?k |} ?source =>
      exact (@starting_not_ready state target k source Hunique Hready) end.
Qed.
Lemma next_commit_incoming tf before after owner : step tf before after -> committing before owner ->
  D.leq (R.aggregate (R.cfg_state after) owner) (R.sigma_value (R.cfg_state after) owner) = true.
Proof.
  intros Hstep [fr [direct [k [Hcontrol ->]]]]; unfold step, R.next_config in Hstep; rewrite Hcontrol in Hstep.
  destruct (R.set_value (R.cfg_state before) fr direct) as [next next_fr] eqn:Hset.
  inversion Hstep; subst after; change (D.leq (R.aggregate next (R.frame_owner fr)) (R.sigma_value next (R.frame_owner fr)) = true).
  pose proof (@commit_footprint (R.cfg_state before) fr direct next next_fr Hset) as Hview.
  unfold R.aggregate; rewrite (commit_contributions Hview); eapply DL.leq_trans;
    [apply DL.join_upper_right |exact (@commit_sound (R.cfg_state before) fr direct next next_fr Hset)].
Qed.
Theorem next_incoming_safe tf before after : NoDup (active_owners (R.cfg_control after)) ->
  incoming_safe before -> step tf before after -> incoming_safe after.
Proof.
  intros Hunique Hsafe Hstep owner Hready.
  destruct (@next_incoming_origin tf before after Hunique Hstep owner Hready) as [Hbefore |Hcommit].
  - eapply next_incoming_bound; [exact Hunique |exact Hstep |exact Hready |apply Hsafe; exact Hbefore].
  - eapply next_commit_incoming; eauto.
Qed.

Theorem next_settled_store tf before after : frames_live before -> waiting_control before ->
  inhabited (observing_control tf before) -> settled_store tf before -> step tf before after -> settled_store tf after.
Proof.
  intros Hframes Hwaiting [Hobserved] Hsettled Hstep owner Hsolved Hidle.
  destruct (@next_idle_origin tf before after Hstep owner Hidle) as [Hbefore |[fr [k [Hcontrol [Hreturn Heq]]]]].
  - destruct (@next_solved_origin tf before after Hframes Hwaiting Hstep owner Hsolved) as [Hold |[Hq |Ha]];
      [|exfalso; exact (proj1 Hidle Hq) |exfalso; exact (proj2 Hidle Ha)].
    destruct (Hsettled owner Hold Hbefore) as [Hdone]; constructor.
    eapply completed_moved; [eapply next_idle_snapshot; eauto |eapply next_preserves_live; exact Hstep |exact (proj1 Hidle) |exact Hdone].
  - subst owner; unfold observing_control in Hobserved; rewrite Hcontrol in Hobserved;
      destruct Hobserved as [Hguarded Hstack].
    assert (Hdone : completed_observation tf (R.cfg_state before) (R.frame_owner fr)).
    { eapply guarded_complete; [| |exact Hguarded].
      - eapply live_reference_solved; [exact Hframes |rewrite Hcontrol; reflexivity].
      - intro Hin; destruct (@next_queue_covered tf before after Hstep (R.frame_owner fr) Hin) as [Hq |Ha];
          [exact (proj1 Hidle Hq) |exact (proj2 Hidle Ha)]. }
    constructor; eapply completed_moved; [|eapply next_preserves_live; exact Hstep |exact (proj1 Hidle) |exact Hdone].
    unfold step, R.next_config in Hstep; rewrite Hcontrol in Hstep.
    destruct (R.queue_peek (R.queue (R.cfg_state before))) as [head|].
    + destruct (V.eq_dec head (R.frame_owner fr)); [destruct (R.queue_pop (R.queue (R.cfg_state before))) as [[popped rest]|]; inversion Hstep; subst after; cbn [R.cfg_control] in Hreturn; discriminate |].
      destruct (R.rank_lt (R.cfg_state before) (R.frame_owner fr) head);
        [destruct (R.queue_pop (R.queue (R.cfg_state before))) as [[popped rest]|]; inversion Hstep; subst after; cbn [R.cfg_control] in Hreturn; discriminate |].
      inversion Hstep; subst after; apply snapshot_close.
    + inversion Hstep; subst after; apply snapshot_close.
Qed.

Record semantic_invariant tf c : Prop := {
  invariant_frames : frames_live c;
  invariant_waiting : waiting_control c;
  invariant_observing : inhabited (observing_control tf c);
  invariant_settled : settled_store tf c;
  invariant_incoming : incoming_safe c
}.
Lemma semantic_initial tf roots : semantic_invariant tf (R.initial_config roots).
Proof.
  constructor; [constructor |exact I |constructor; exact tt | |].
  - intros owner [value Hvalue] Hidle; change (M.lookup (M.empty D.t) owner = Some value) in Hvalue;
      rewrite ML.lookup_empty in Hvalue; discriminate.
  - intros owner Hready; unfold R.aggregate, R.lookup_map; cbn [R.cfg_state R.initial_config R.empty_state R.contributions];
      rewrite ML.lookup_empty, ML.values_empty; apply DL.bottom_least.
Qed.
Theorem next_semantic_invariant tf before after : active_ordered before -> active_ordered after ->
  semantic_invariant tf before -> step tf before after -> semantic_invariant tf after.
Proof.
  intros Horder Hnext [Hframes Hwaiting Hobserving Hsettled Hincoming] Hstep; constructor.
  - eapply next_frames_live; eauto.
  - eapply next_waiting_control; eauto.
  - eapply next_observing_control; eauto.
  - eapply next_settled_store; eauto.
  - eapply next_incoming_safe; [eapply ordered_unique; exact Hnext |exact Hincoming |exact Hstep].
Qed.
Theorem reachable_semantic_invariant tf roots c :
  steps tf (R.initial_config roots) c -> semantic_invariant tf c.
Proof.
  intro Hpath.
  assert (Hwf : config_wf (fun _ => True) (R.initial_config roots)) by (split; [apply store_initial |apply Forall_forall; auto]).
  assert (Horder : active_ordered (R.initial_config roots)) by constructor.
  pose proof (semantic_initial tf roots) as Hinitial.
  revert Hwf Horder Hinitial; induction Hpath; auto; intros Hwf Horder Hfirst.
  assert (Hnext : active_ordered next) by (eapply next_active_ordered; eauto).
  apply IHHpath; [eapply next_configuration_wf; [intros owner _; apply code_unrestricted |exact Hwf |exact H] |exact Hnext |].
  eapply next_semantic_invariant with (before := before); [exact Horder |exact Hnext |exact Hfirst |exact H].
Qed.

(** Partial correctness follows from the observations maintained by the
    machine. No correctness premise or upper-bound update law is required. *)
Theorem successful_run_correct fuel tf roots final :
  R.solve_fuel fuel tf roots = Some final -> correct_final_state tf roots final.
Proof.
  intro Hrun; split; [eapply successful_roots_materialized; exact Hrun |].
  destruct (@successful_path fuel tf roots final Hrun) as [Hpath Hquiet].
  pose proof (@reachable_semantic_invariant tf roots (terminal final) Hpath) as Hsem.
  intros owner Hsolved.
  assert (Hidle : forall x, idle (terminal final) x).
  { intro x; split; [change (~ In x (R.queue final)); rewrite Hquiet; auto |cbn; auto]. }
  destruct (invariant_settled Hsem Hsolved (Hidle owner)) as [Hdone].
  apply (completed_is_post_solution Hdone); intros target raw Hin.
  apply (invariant_incoming Hsem); split; [exact (proj1 (Hidle target)) |left; exact (proj2 (Hidle target))].
Qed.
Theorem successful_run_least fuel tf roots (finite : Sem.finite_system tf roots) final :
  (forall side x phase old input upper, D.leq old upper = true -> D.leq input upper = true ->
    D.leq (snd (U.update side x phase old input)) upper = true) ->
  source_strict_on tf (Sem.support finite) roots -> Sem.system_monotone_on tf (Sem.support finite) ->
  R.solve_fuel fuel tf roots = Some final -> Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
  intros Hbounded Hstrict Hmono Hrun; eapply correct_successful_run_least;
    [exact Hbounded |exact Hstrict |exact Hmono |exact (@successful_run_correct fuel tf roots final Hrun) |exact Hrun].
Qed.

(** Generation by a finite support is separate from rank validity. This
    keeps ordinary partial correctness independent of finite-system laws. *)
Lemma generated_observe support st target : RF.generated support (R.ranking st) -> In target support ->
  RF.generated support (R.ranking (R.observe st target)).
Proof.
  intros Hg Htarget; unfold R.observe; destruct (Ranks.observe (R.ranking st) target) as [next rank] eqn:Hobs; cbn.
  eapply RF.generated_observe; eauto.
Qed.
Lemma next_generated support tf before after : config_wf (fun x => In x support) before ->
  RF.generated support (R.ranking (R.cfg_state before)) -> step tf before after ->
  RF.generated support (R.ranking (R.cfg_state after)).
Proof.
  intros [Hst Hrefs] Hgenerated Hstep; destruct before as [st ctrl];
    unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep, Hgenerated, Hrefs.
  destruct ctrl; cbn [R.cfg_control control_refs] in Hstep, Hrefs;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep; primitive_ranks.
  all: cbn [R.cfg_state R.cfg_control R.with_queue R.ranking R.requeue_changed_controlled_owner R.enqueue] in *;
    repeat first [rewrite materialize_rank |rewrite close_rank
      |match goal with Hr : R.ranking _ = R.ranking _ |- _ => rewrite Hr; clear Hr end
      |progress cbn [R.enqueue R.with_queue R.ranking]];
    try exact Hgenerated.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try match goal with Hcode : Sem.rhs_supported _ _ |- _ =>
    pose proof (code_child_supported Hcode) as Hchildren; cbn in Hchildren; destruct Hchildren end.
  all: try match goal with Hroots : Forall _ (_ :: _) |- _ => inversion Hroots; subst end.
  all: try solve [apply generated_observe; [exact Hgenerated |assumption]].
  all: try solve [apply generated_observe; [exact Hgenerated |eapply Forall_inv; eassumption]].
  all: match goal with |- context [if ?b then _ else _] => destruct b end.
  all: cbn [R.enqueue R.with_queue R.ranking]; apply generated_observe; [exact Hgenerated |assumption].
Qed.
Theorem reachable_generated tf roots (finite : Sem.finite_system tf roots) c :
  steps tf (R.initial_config roots) c -> RF.generated (Sem.support finite) (R.ranking (R.cfg_state c)).
Proof.
  intro Hpath.
  assert (Hwf : config_wf (fun x => In x (Sem.support finite)) (R.initial_config roots)) by
    (eapply reachable_configuration_wf; constructor).
  assert (Hg : RF.generated (Sem.support finite) (R.ranking (R.cfg_state (R.initial_config roots)))) by apply RF.generated_empty.
  revert Hwf Hg; induction Hpath; auto; intros Hwf Hg; apply IHHpath.
  - eapply next_configuration_wf; eauto using Sem.system_supported.
  - eapply next_generated; eauto.
Qed.
Theorem reachable_rank_bound tf roots (finite : Sem.finite_system tf roots) c owner rank :
  steps tf (R.initial_config roots) c -> Ranks.lookup (R.ranking (R.cfg_state c)) owner = Some rank -> rank < RF.bound (Sem.support finite).
Proof.
  intros Hpath Hlookup; eapply RF.generated_lookup_bound;
    [exact (store_valid (proj1 (@reachable_configuration_wf tf roots finite c Hpath)))
    |exact (@reachable_generated tf roots finite c Hpath) |exact Hlookup].
Qed.

(** Reset scopes lie at or below the source and strictly below the target.
    This is the reason a recursive child cannot refill its parent's credit. *)
Definition rank_le order x y := x = y \/ R.ranking_lt order x y = true.
Lemma rank_le_trans order x y z : rank_le order x y -> rank_le order y z -> rank_le order x z.
Proof. unfold rank_le; intros [-> |Hxy] [-> |Hyz]; auto; right; eapply lt_trans; eauto. Qed.
Lemma rank_le_extends before after x y : extends before after -> rank_le before x y -> rank_le after x y.
Proof.
  intros Hext [-> |Hlt]; [now left |right].
  destruct (@lt_ranks before x y Hlt) as [rx [ry [Hx [Hy _]]]].
  rewrite (@lt_stable before after x y Hext (ex_intro _ rx Hx) (ex_intro _ ry Hy)); exact Hlt.
Qed.
Lemma lt_extends before after x y : extends before after ->
  R.ranking_lt before x y = true -> R.ranking_lt after x y = true.
Proof.
  intros Hext Hlt; destruct (@lt_ranks before x y Hlt) as [rx [ry [Hx [Hy _]]]].
  rewrite (@lt_stable before after x y Hext (ex_intro _ rx Hx) (ex_intro _ ry Hy)); exact Hlt.
Qed.
Definition reset_scoped st := forall scope source target,
  In (source,target) (R.lookup_reset_ids (R.reset_at_close st) scope) ->
  rank_le (R.ranking st) scope source /\ R.rank_lt st scope target = true.
Definition frame_scoped st fr := rank_le (R.ranking st) (R.frame_min_scope fr) (R.frame_owner fr).
Fixpoint scoped_stack st k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => True
  | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest
  | R.KDead fr _ _ rest | R.KDrain fr rest => frame_scoped st fr /\ scoped_stack st rest
  end.
Definition scoped_control st ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
  | R.StartEpisode _ k | R.Return k => scoped_stack st k
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k =>
      frame_scoped st fr /\ scoped_stack st k
  end.
Definition scoped_config c := reset_scoped (R.cfg_state c) /\
  scoped_control (R.cfg_state c) (R.cfg_control c).
Lemma scoped_frame_extends before after fr : extends (R.ranking before) (R.ranking after) ->
  frame_scoped before fr -> frame_scoped after fr.
Proof. apply rank_le_extends. Qed.
Lemma scoped_stack_extends before after k : extends (R.ranking before) (R.ranking after) ->
  scoped_stack before k -> scoped_stack after k.
Proof. intros Hext; induction k; cbn; intuition eauto using scoped_frame_extends. Qed.
Lemma scoped_layout before after : extends (R.ranking before) (R.ranking after) ->
  R.reset_at_close after = R.reset_at_close before -> reset_scoped before -> reset_scoped after.
Proof.
  intros Hext Hresets H scope source target Hin; rewrite Hresets in Hin.
  destruct (H scope source target Hin) as [Hsource Htarget]; split;
    eauto using rank_le_extends, lt_extends.
Qed.
Lemma removed_member id ids observed : In observed (R.remove_cell_id id ids) -> In observed ids.
Proof.
  induction ids as [|head rest IH]; cbn; [auto |].
  destruct (R.cell_id_eq_dec id head); cbn; intuition.
Qed.
Lemma added_member id ids observed : In observed (R.add_cell_id id ids) -> observed = id \/ In observed ids.
Proof. unfold R.add_cell_id; destruct (in_dec R.cell_id_eq_dec id ids); cbn; intuition congruence. Qed.
Lemma reset_lookup_put table scope ids observed :
  R.lookup_reset_ids (M.update table scope ids) observed =
    if V.eq_dec observed scope then ids else R.lookup_reset_ids table observed.
Proof.
  unfold R.lookup_reset_ids; destruct (V.eq_dec observed scope) as [-> |Hneq];
    [rewrite ML.lookup_update_same |rewrite ML.lookup_update_other]; auto.
Qed.
Lemma scoped_remove st previous id : reset_scoped st ->
  forall scope source target,
    In (source,target) (R.lookup_reset_ids (R.remove_registration (R.reset_at_close st) previous id) scope) ->
    rank_le (R.ranking st) scope source /\ R.rank_lt st scope target = true.
Proof.
  intros H scope source target Hin; unfold R.remove_registration in Hin;
    rewrite reset_lookup_put in Hin; destruct (V.eq_dec scope previous) as [-> |Hneq];
    eapply H; eauto using removed_member.
Qed.
Lemma scoped_register st source target scope phase : reset_scoped st ->
  rank_le (R.ranking st) scope source -> reset_scoped (R.register_reset st source target scope phase).
Proof.
  intros Hreset Hsource; unfold R.register_reset.
  set (requested := if Features.restart_side_phases then
    if R.rank_lt st scope target then Some scope else None else None).
  set (same := R.same_scope (R.side_reset_at (R.stored_side_cell st source target)) requested).
  set (without := if same then R.reset_at_close st else
    match R.side_reset_at (R.stored_side_cell st source target) with
    | Some previous => R.remove_registration (R.reset_at_close st) previous (source,target)
    | None => R.reset_at_close st end).
  assert (Hwithout : forall location x y, In (x,y) (R.lookup_reset_ids without location) ->
    rank_le (R.ranking st) location x /\ R.rank_lt st location y = true).
  { unfold without; destruct same; [exact Hreset |].
    destruct (R.side_reset_at (R.stored_side_cell st source target));
      [apply scoped_remove; exact Hreset |exact Hreset]. }
  unfold reset_scoped; cbn [R.with_cells_and_resets R.reset_at_close R.ranking R.rank_lt].
  destruct same; [exact Hwithout |].
  unfold requested; destruct Features.restart_side_phases; [|exact Hwithout].
  destruct (R.rank_lt st scope target) eqn:Heligible; [|exact Hwithout].
  intros location x y Hin; unfold R.add_registration in Hin; rewrite reset_lookup_put in Hin.
  destruct (V.eq_dec location scope) as [-> |Hneq]; [|apply Hwithout; exact Hin].
  apply added_member in Hin; destruct Hin as [Heq |Hin];
    [inversion Heq; subst; auto |apply Hwithout; exact Hin].
Qed.
Lemma scoped_close st owner : reset_scoped st -> reset_scoped (R.reset_registered_cells st owner).
Proof.
  intro H; unfold R.reset_registered_cells; destruct Features.restart_side_phases; auto.
  intros scope source target Hin; cbn in Hin |- *; rewrite reset_lookup_put in Hin.
  destruct (V.eq_dec scope owner); [contradiction |apply H; exact Hin].
Qed.
Lemma scoped_materialize st owner : reset_scoped st -> reset_scoped (R.materialize st owner).
Proof. intro H; eapply scoped_layout with (before := st); [rewrite materialize_rank; apply extends_refl |unfold R.materialize; destruct (M.lookup (R.sigma st) owner); reflexivity |exact H]. Qed.
Lemma scoped_observe st target : reset_scoped st -> reset_scoped (R.observe st target).
Proof. intro H; eapply scoped_layout with (before := st); [apply observe_extends |unfold R.observe; destruct (Ranks.observe (R.ranking st) target); reflexivity |exact H]. Qed.
Lemma scoped_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  reset_scoped st -> frame_scoped st fr -> reset_scoped next /\ frame_scoped next next_fr.
Proof.
  intros Hget Hreset Hframe; split.
  - destruct (get_layout Hget) as [Hr [_ [_ [_ [Hresets _]]]]];
      eapply scoped_layout with (before := st); [rewrite Hr; apply extends_refl |exact Hresets |exact Hreset].
  - unfold R.complete_get in Hget; destruct (R.rank_lt st (R.frame_owner fr) target);
      destruct (R.rank_lt st target (R.frame_min_scope fr)) eqn:Hmin;
      split_program Hget; unfold frame_scoped in *; cbn in *;
      unfold R.materialize; destruct (M.lookup _ target); cbn; try exact Hframe.
    all: eapply rank_le_trans; [right; exact Hmin |exact Hframe].
Qed.
Lemma scoped_write st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) ->
  reset_scoped st -> frame_scoped st fr -> reset_scoped next.
Proof.
  intros Hwrite Hreset Hframe; unfold R.write_side_contribution in Hwrite.
  destruct (U.update _ _ _ _ _) as [phase value]; inversion Hwrite; subst next.
  apply scoped_register.
  - eapply scoped_layout with (before := st); [| |exact Hreset]; unfold R.promote_side_target, R.promote_controlled;
      destruct (R.rank_lt st target (R.frame_owner fr)); cbn; auto using extends_refl.
  - unfold R.promote_side_target, R.promote_controlled;
      destruct (R.rank_lt st target (R.frame_owner fr)); exact Hframe.
Qed.
Lemma scoped_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  reset_scoped st -> frame_scoped st fr -> reset_scoped next /\ frame_scoped next next_fr.
Proof.
  intros Hset Hreset Hframe; pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview; split.
  - eapply scoped_layout with (before := st); [rewrite (commit_ranking Hview); apply extends_refl |exact (commit_resets Hview) |exact Hreset].
  - unfold R.set_value in Hset; split_program Hset; exact Hframe.
Qed.

Lemma scoped_queue st q : reset_scoped st -> reset_scoped (R.with_queue st q).
Proof. auto. Qed.
Lemma scoped_enqueue st x : reset_scoped st -> reset_scoped (R.enqueue st x).
Proof. auto. Qed.
Lemma scoped_publish st fr : reset_scoped st -> reset_scoped (R.publish_targets st fr).
Proof. auto. Qed.
Lemma scoped_requeue before after owner : reset_scoped after ->
  reset_scoped (R.requeue_changed_controlled_owner before after owner).
Proof. auto. Qed.
Lemma scoped_fresh st owner phase : frame_scoped st (R.fresh_frame st owner phase).
Proof. left; reflexivity. Qed.
Lemma scoped_side_frame st fr target input : frame_scoped st fr ->
  frame_scoped st (R.with_frame_side fr target input).
Proof. auto. Qed.
Lemma next_scoped_config tf before after : scoped_config before -> step tf before after -> scoped_config after.
Proof.
  intros [Hreset Hcontrol] Hstep; pose proof (next_ranking_extends Hstep) as Hext.
  destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep, Hreset, Hcontrol, Hext.
  destruct ctrl as [|roots|roots|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    unfold scoped_control in Hcontrol; cbn [R.cfg_control] in Hstep;
    try match type of Hcontrol with _ /\ _ => destruct Hcontrol as [Hframe Hstack] end.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|] eqn:Hpop; [|discriminate].
    inversion Hstep; subst after; split; [exact Hreset |exact I].
  - destruct roots as [|root roots].
    + inversion Hstep; subst after; split; [exact Hreset |exact I].
    + destruct (R.is_materialized (R.observe st root) root); inversion Hstep; subst after.
      all: split; [apply scoped_observe; exact Hreset |exact I].
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|] eqn:Hpop;
      inversion Hstep; subst after.
    all: split; [exact Hreset |exact I].
  - inversion Hstep; subst after; split; [apply scoped_materialize; exact Hreset |].
    split; [apply scoped_fresh |eapply scoped_stack_extends; [exact Hext |exact Hcontrol]].
  - destruct body as [direct|target tail|target raw tail|target tail].
    + inversion Hstep; subst after; split; [exact Hreset |split; [exact Hframe |eapply scoped_stack_extends; [exact Hext |exact Hstack]]].
    + set (st0 := R.observe st target) in *.
      assert (Hreset0 : reset_scoped st0) by (apply scoped_observe; exact Hreset).
      assert (Hframe0 : frame_scoped st0 fr) by
        (eapply scoped_frame_extends; [apply observe_extends |exact Hframe]).
      destruct (negb (R.is_materialized st0 target) && R.rank_lt st0 (R.frame_owner fr) target).
      * inversion Hstep; subst after; split; [exact Hreset0 |].
        split; [exact Hframe0 |eapply scoped_stack_extends; [exact Hext |exact Hstack]].
      * set (st1 := if R.is_materialized st0 target then st0 else R.enqueue st0 target) in *.
        assert (Hreset1 : reset_scoped st1) by (unfold st1; destruct (R.is_materialized st0 target); exact Hreset0).
        assert (Hframe1 : frame_scoped st1 fr) by (unfold st1; destruct (R.is_materialized st0 target); exact Hframe0).
        destruct (R.complete_get st1 fr target) as [[next next_fr] value] eqn:Hget.
        inversion Hstep; subst after; destruct (scoped_get Hget Hreset1 Hframe1) as [Hnext Hfr].
        split; [exact Hnext |split; [exact Hfr |eapply scoped_stack_extends; [exact Hext |exact Hstack]]].
    + unfold R.record_side_input in Hstep.
      destruct (R.write_side_contribution (R.observe st target)
        (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) target
        (R.accumulated_side_input fr target raw)) as [next changed] eqn:Hwrite.
      assert (Hnext : reset_scoped next).
      { eapply scoped_write; [exact Hwrite |apply scoped_observe; exact Hreset |].
        apply scoped_side_frame; eapply scoped_frame_extends; [apply observe_extends |exact Hframe]. }
      unfold R.continue_side in Hstep; split_program Hstep; split;
        [exact Hnext | |apply scoped_enqueue; exact Hnext | |exact Hnext |].
      all: cbn [R.cfg_state R.cfg_control scoped_control scoped_stack]; split;
        [apply scoped_side_frame; eapply scoped_frame_extends; [exact Hext |exact Hframe]
        |eapply scoped_stack_extends; [exact Hext |exact Hstack]].
    + destruct (R.is_materialized (R.observe st target) target);
        [|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target)];
        inversion Hstep; subst after; split;
        [apply scoped_observe; exact Hreset | |apply scoped_observe; exact Hreset | |
         apply scoped_materialize, scoped_enqueue, scoped_observe; exact Hreset |].
      all: split; [eapply scoped_frame_extends; [exact Hext |exact Hframe]
        |eapply scoped_stack_extends; [exact Hext |exact Hstack]].
  - destruct pending as [|target rest].
    + inversion Hstep; subst after; split; [exact Hreset |split; [exact Hframe |eapply scoped_stack_extends; [exact Hext |exact Hstack]]].
    + destruct (S.mem target (R.frame_current_targets fr)).
      * inversion Hstep; subst after; split; [exact Hreset |split; [exact Hframe |eapply scoped_stack_extends; [exact Hext |exact Hstack]]].
      * destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite.
        assert (Hnext : reset_scoped next) by (eapply scoped_write; eauto).
        unfold R.continue_dead in Hstep; split_program Hstep; split;
          [exact Hnext | |apply scoped_enqueue; exact Hnext | |exact Hnext |].
        all: split; [eapply scoped_frame_extends; [exact Hext |exact Hframe]
          |eapply scoped_stack_extends; [exact Hext |exact Hstack]].
  - destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
    inversion Hstep; subst after; destruct (@scoped_commit st fr direct next next_fr Hset Hreset Hframe) as [Hnext Hfr].
    split; [apply scoped_requeue; exact Hnext |split; [exact Hfr |]].
    eapply scoped_stack_extends; [exact Hext |exact Hstack].
  - destruct (R.queue_peek (R.queue st)) as [head|].
    + destruct (V.eq_dec head (R.frame_owner fr)).
      * destruct (R.queue_pop (R.queue st)) as [[popped rest]|]; [|discriminate].
        inversion Hstep; subst after; split; [exact Hreset |split; [apply scoped_fresh |]].
        eapply scoped_stack_extends; [exact Hext |exact Hstack].
      * destruct (R.rank_lt st (R.frame_owner fr) head).
        -- destruct (R.queue_pop (R.queue st)) as [[popped rest]|]; [|discriminate].
           inversion Hstep; subst after; split; [exact Hreset |split; [exact Hframe |eapply scoped_stack_extends; [exact Hext |exact Hstack]]].
        -- inversion Hstep; subst after; split; [apply scoped_close; exact Hreset |].
           eapply scoped_stack_extends; [exact Hext |exact Hstack].
    + inversion Hstep; subst after; split; [apply scoped_close; exact Hreset |].
      eapply scoped_stack_extends; [exact Hext |exact Hstack].
  - destruct k as [|remaining|fr target tail k|fr tail k|fr tail k|fr direct pending k|fr k]; cbn [scoped_stack] in Hcontrol;
      try match type of Hcontrol with _ /\ _ => destruct Hcontrol as [Hframe Hstack] end.
    all: try solve [inversion Hstep; subst after; split; [exact Hreset |exact I]].
    all: try solve [inversion Hstep; subst after; split;
      [exact Hreset |split; [exact Hframe |eapply scoped_stack_extends; [exact Hext |exact Hstack]]]].
    destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:Hget;
      inversion Hstep; subst after; destruct (scoped_get Hget Hreset Hframe) as [Hnext Hfr].
    split; [exact Hnext |split; [exact Hfr |eapply scoped_stack_extends; [exact Hext |exact Hstack]]].
Qed.
Theorem reachable_scoped_config tf roots c : steps tf (R.initial_config roots) c -> scoped_config c.
Proof.
  intro Hpath; assert (Hinitial : scoped_config (R.initial_config roots)).
  { split; [|exact I]; intros scope source target Hin.
    change (In (source,target) (R.lookup_reset_ids (M.empty (list R.side_cell_id)) scope)) in Hin.
    unfold R.lookup_reset_ids in Hin; rewrite ML.lookup_empty in Hin; contradiction. }
  revert Hinitial; induction Hpath; auto; intro Hfirst; apply IHHpath; eapply next_scoped_config; eauto.
Qed.

Lemma row_lookup_other {A} (rows : M.t (M.t A)) outer inner value x y :
  (x,y) <> (outer,inner) ->
  M.lookup (R.lookup_map (R.update_map rows outer inner value) x) y =
    M.lookup (R.lookup_map rows x) y.
Proof.
  intro Hneq; destruct (V.eq_dec x outer) as [-> |Hx].
  - unfold R.update_map, R.lookup_map; rewrite ML.lookup_update_same.
    apply ML.lookup_update_other; congruence.
  - rewrite row_other; auto.
Qed.
Lemma reset_cells_other ids cells source target :
  ~ In (source,target) ids ->
  M.lookup (R.lookup_map (R.reset_cells ids cells) source) target =
    M.lookup (R.lookup_map cells source) target.
Proof.
  revert cells; induction ids as [|[x y] ids IH]; intros cells Hnot; cbn; [reflexivity |].
  rewrite IH; [apply row_lookup_other; intro Heq; apply Hnot; left; symmetry; exact Heq
    |intro Hin; apply Hnot; right; exact Hin].
Qed.
Lemma rank_le_no_cycle order x y : R.ranking_lt order x y = true -> ~ rank_le order y x.
Proof.
  intros Hxy [Heq |Hyx]; [subst; rewrite lt_irrefl in Hxy; discriminate |].
  pose proof (@lt_trans order x y x Hxy Hyx) as Hfalse; rewrite lt_irrefl in Hfalse; discriminate.
Qed.
Lemma higher_close_cells st owner child source target : reset_scoped st ->
  R.rank_lt st owner child = true -> (source = owner \/ target = owner) ->
  R.stored_side_cell (R.reset_registered_cells st child) source target = R.stored_side_cell st source target.
Proof.
  intros Hscoped Hhigher Hincident; unfold R.reset_registered_cells;
    destruct Features.restart_side_phases; [|reflexivity].
  unfold R.stored_side_cell; cbn; rewrite reset_cells_other; [reflexivity |].
  intro Hin; destruct (Hscoped child source target Hin) as [Hs Ht].
  destruct Hincident as [-> | ->].
  - exact (@rank_le_no_cycle (R.ranking st) owner child Hhigher Hs).
  - apply (@rank_le_no_cycle (R.ranking st) owner child Hhigher); right; exact Ht.
Qed.
Definition side_credit st source target := UL.remaining_changes
  (R.side_phase (R.stored_side_cell st source target)) (R.stored_contribution st source target).
Lemma side_credit_layout before after source target :
  R.side_cells after = R.side_cells before -> R.contributions after = R.contributions before ->
  side_credit after source target = side_credit before source target.
Proof. intros Hcells Hcontrib; unfold side_credit, R.stored_side_cell, R.stored_contribution; now rewrite Hcells, Hcontrib. Qed.
Lemma higher_close_credit st owner child source target : reset_scoped st ->
  R.rank_lt st owner child = true -> (source = owner \/ target = owner) ->
  side_credit (R.reset_registered_cells st child) source target = side_credit st source target.
Proof.
  intros Hreset Hhigher Hincident; unfold side_credit; rewrite (@higher_close_cells st owner child source target Hreset Hhigher Hincident).
  unfold R.stored_contribution, R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity.
Qed.
Lemma promoted_side_credit st fr written source target :
  side_credit (R.promote_side_target st fr written) source target = side_credit st source target.
Proof. unfold R.promote_side_target, R.promote_controlled; destruct (R.rank_lt st written (R.frame_owner fr)); reflexivity. Qed.
Lemma side_credit_put st source target scope phase value :
  side_credit (R.register_reset (R.with_contributions st
    (R.update_map (R.contributions st) target source value)) source target scope phase) source target =
    UL.remaining_changes phase value.
Proof.
  unfold side_credit, R.stored_side_cell, R.stored_contribution, R.register_reset;
    cbn [R.with_cells_and_resets R.with_contributions R.side_cells R.contributions];
    rewrite !row_lookup; reflexivity.
Qed.
Lemma aggregate_equivalent_put st source target value : eqv value (R.stored_contribution st source target) ->
  eqv (R.aggregate (R.with_contributions st (R.update_map (R.contributions st) target source value)) target)
    (R.aggregate st target).
Proof.
  intro Hvalue; unfold R.aggregate, R.update_map; cbn; unfold R.lookup_map at 1;
    rewrite ML.lookup_update_same.
  set (row := R.lookup_map (R.contributions st) target) in *.
  destruct (ML.values_update row source value) as [rest [Hnew Hold]].
  eapply eqv_trans; [apply fold_permutation; exact Hnew |].
  unfold R.stored_contribution in Hvalue; fold row in Hvalue;
    destruct (M.lookup row source) as [previous|] eqn:Hlookup.
  - eapply eqv_trans; [apply join_eqv; [exact Hvalue |apply eqv_refl] |].
    exact (eqv_sym (@fold_permutation (M.values row) (previous :: rest) Hold)).
  - eapply eqv_trans; [apply join_eqv; [exact Hvalue |apply eqv_refl] |].
    eapply eqv_trans; [apply join_bottom |exact (eqv_sym (@fold_permutation (M.values row) rest Hold))].
Qed.
Lemma side_credit_write st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  side_credit next (R.frame_owner fr) target <= side_credit st (R.frame_owner fr) target /\
  (changed = true -> side_credit next (R.frame_owner fr) target < side_credit st (R.frame_owner fr) target).
Proof.
  unfold R.write_side_contribution.
  set (base := R.promote_side_target st fr target).
  set (phase := R.side_phase (R.stored_side_cell base (R.frame_owner fr) target)).
  set (old := R.stored_contribution base (R.frame_owner fr) target).
  destruct (U.update true target phase old input) as [new_phase value] eqn:Hupdate.
  intro Hwrite; inversion Hwrite; subst next changed; clear Hwrite; rewrite side_credit_put.
  rewrite <- (promoted_side_credit st fr target (R.frame_owner fr) target).
  unfold side_credit; fold base; fold phase old.
  pose proof (UL.remaining_changes_nonincreasing true target phase old input) as Hcredit;
    rewrite Hupdate in Hcredit; cbn in Hcredit; split; [exact Hcredit |].
  intro Hchanged; pose proof (@UL.update_change_consumes true target phase old input) as Hstrict;
    rewrite Hupdate in Hstrict; cbn in Hstrict; apply Hstrict.
  intro Heq; apply negb_true_iff in Hchanged.
  assert (Hagg : eqv
    (R.aggregate (R.with_contributions base (R.update_map (R.contributions base) target (R.frame_owner fr) value)) target)
    (R.aggregate base target)) by (apply aggregate_equivalent_put; exact Heq).
  unfold R.aggregate, R.register_reset in Hchanged; cbn [R.with_cells_and_resets R.contributions] in Hchanged.
  apply (proj2 (eqv_bool _ _)) in Hagg; unfold R.aggregate in Hagg; congruence.
Qed.
Lemma side_credit_write_other st fr written input next changed source target :
  R.write_side_contribution st fr written input = (next,changed) ->
  (source,target) <> (R.frame_owner fr,written) -> side_credit next source target = side_credit st source target.
Proof.
  intros Hwrite Hother; unfold R.write_side_contribution in Hwrite;
    destruct (U.update _ _ _ _ _) as [phase value]; inversion Hwrite; subst next.
  unfold side_credit, R.stored_side_cell, R.stored_contribution, R.register_reset;
    cbn [R.with_cells_and_resets R.with_contributions R.side_cells R.contributions];
    rewrite !row_lookup_other by congruence.
  unfold R.promote_side_target, R.promote_controlled;
    destruct (R.rank_lt st written (R.frame_owner fr)); reflexivity.
Qed.
Lemma side_credit_write_all st fr written input next changed source target :
  R.write_side_contribution st fr written input = (next,changed) ->
  side_credit next source target <= side_credit st source target.
Proof.
  intro Hwrite; destruct (R.cell_id_eq_dec (source,target) (R.frame_owner fr,written)) as [Heq |Hneq].
  - inversion Heq; subst; apply (proj1 (side_credit_write Hwrite)).
  - rewrite (side_credit_write_other Hwrite Hneq); lia.
Qed.

Arguments side_credit_write_all {st fr written input next changed} source target _.

Fixpoint sum_over (f : V.t -> nat) (support : list V.t) : nat :=
  match support with [] => 0 |x :: xs => f x + sum_over f xs end.
Lemma sum_over_le f g support : (forall x, In x support -> f x <= g x) -> sum_over f support <= sum_over g support.
Proof. induction support as [|x xs IH]; cbn; intros H; [lia |]; assert (Hhead := H x (or_introl eq_refl)); assert (Htail : sum_over f xs <= sum_over g xs) by (apply IH; auto); lia. Qed.
Lemma sum_over_lt f g support x : In x support -> f x < g x ->
  (forall y, In y support -> f y <= g y) -> sum_over f support < sum_over g support.
Proof.
  induction support as [|head rest IH]; cbn; [contradiction |].
  intros [<- |Hin] Hstrict Hle.
  - assert (Htail : sum_over f rest <= sum_over g rest) by (apply sum_over_le; auto); lia.
  - assert (Hhead := Hle head (or_introl eq_refl)).
    assert (Htail : sum_over f rest < sum_over g rest) by (apply IH; auto); lia.
Qed.
Definition incident_credit support st owner :=
  sum_over (fun target => side_credit st owner target) support +
  sum_over (fun source => side_credit st source owner) support.
Lemma incident_credit_write support st fr target input next changed owner :
  R.write_side_contribution st fr target input = (next,changed) ->
  incident_credit support next owner <= incident_credit support st owner.
Proof.
  intro Hwrite; unfold incident_credit;
    pose proof (sum_over_le (fun t => side_credit next owner t) (fun t => side_credit st owner t) support
      (fun t _ => side_credit_write_all owner t Hwrite)) as Hsource;
    pose proof (sum_over_le (fun s => side_credit next s owner) (fun s => side_credit st s owner) support
      (fun s _ => side_credit_write_all s owner Hwrite)) as Htarget; lia.
Qed.
Lemma incident_credit_write_strict support st fr target input next owner :
  R.write_side_contribution st fr target input = (next,true) -> In (R.frame_owner fr) support -> In target support ->
  (owner = R.frame_owner fr \/ owner = target) ->
  incident_credit support next owner < incident_credit support st owner.
Proof.
  intros Hwrite Hsource Htarget Hincident;
    pose proof (proj2 (side_credit_write Hwrite) eq_refl) as Hstrict.
  unfold incident_credit; destruct Hincident as [-> | ->].
  - pose proof (sum_over_lt (fun t => side_credit next (R.frame_owner fr) t)
      (fun t => side_credit st (R.frame_owner fr) t) support target Htarget Hstrict
      (fun t _ => side_credit_write_all (R.frame_owner fr) t Hwrite)) as Hout.
    pose proof (sum_over_le (fun s => side_credit next s (R.frame_owner fr))
      (fun s => side_credit st s (R.frame_owner fr)) support
      (fun s _ => side_credit_write_all s (R.frame_owner fr) Hwrite)) as Hin; lia.
  - pose proof (sum_over_lt (fun s => side_credit next s target) (fun s => side_credit st s target)
      support (R.frame_owner fr) Hsource Hstrict (fun s _ => side_credit_write_all s target Hwrite)) as Hin.
    pose proof (sum_over_le (fun t => side_credit next target t) (fun t => side_credit st target t)
      support (fun t _ => side_credit_write_all target t Hwrite)) as Hout; lia.
Qed.
Lemma incident_credit_higher_close support st owner child : reset_scoped st -> R.rank_lt st owner child = true ->
  incident_credit support (R.reset_registered_cells st child) owner = incident_credit support st owner.
Proof.
  intros Hreset Hhigher; unfold incident_credit; f_equal.
  - induction support as [|head rest IH]; cbn; [reflexivity |].
    rewrite (@higher_close_credit st owner child owner head Hreset Hhigher (or_introl eq_refl)), IH; reflexivity.
  - induction support as [|head rest IH]; cbn; [reflexivity |].
    rewrite (@higher_close_credit st owner child head owner Hreset Hhigher (or_intror eq_refl)), IH; reflexivity.
Qed.

Definition controlled_mono before after := forall owner,
  S.mem owner (R.controlled before) = true -> S.mem owner (R.controlled after) = true.
Lemma controlled_layout before after : R.controlled after = R.controlled before -> controlled_mono before after.
Proof. intros H owner Hmem; now rewrite H. Qed.
Lemma controlled_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) -> controlled_mono st next.
Proof.
  unfold R.complete_get, R.materialize, R.promote_controlled; intro H; split_program H;
    intros owner Hmem; cbn; try exact Hmem; apply SL.add_spec; auto.
Qed.
Lemma controlled_write st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) -> controlled_mono st next.
Proof.
  unfold R.write_side_contribution, R.promote_side_target, R.promote_controlled, R.register_reset;
    intro H; split_program H; intros owner Hmem; cbn; try exact Hmem; apply SL.add_spec; auto.
Qed.
Lemma controlled_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) -> controlled_mono st next.
Proof. intro H; apply controlled_layout; exact (commit_controlled (@commit_footprint st fr direct next next_fr H)). Qed.
Arguments controlled_commit {st fr direct next next_fr} _.
Theorem next_controlled_mono tf before after : step tf before after -> controlled_mono (R.cfg_state before) (R.cfg_state after).
Proof.
  destruct before as [st ctrl]; unfold step, R.next_config; cbn [R.cfg_state R.cfg_control]; intro Hstep.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead in Hstep; split_program Hstep.
  all: repeat match goal with
  | Hget : R.complete_get _ _ _ = (_,_,_) |- _ =>
      let Hm := fresh "get_controlled" in pose proof (controlled_get Hget) as Hm; clear Hget
  | Hwrite : R.write_side_contribution _ _ _ _ = (_,_) |- _ =>
      let Hm := fresh "write_controlled" in pose proof (controlled_write Hwrite) as Hm; clear Hwrite
  | Hset : R.set_value _ _ _ = (_,_) |- _ =>
      let Hm := fresh "commit_controlled" in pose proof (controlled_commit Hset) as Hm; clear Hset
  end.
  all: intros owner Hmem; cbn [R.cfg_state R.with_queue R.controlled R.enqueue R.publish_targets R.requeue_changed_controlled_owner] in *;
    try exact Hmem; try solve [match goal with Hm : controlled_mono _ _ |- _ => apply Hm; exact Hmem end].
  all: unfold R.observe, R.materialize, R.reset_registered_cells;
    repeat match goal with
    | |- context [match Ranks.observe ?order ?target with _ => _ end] => destruct (Ranks.observe order target)
    | |- context [match M.lookup ?table ?target with _ => _ end] => destruct (M.lookup table target)
    | |- context [if ?b then _ else _] => destruct b
    end; cbn; try exact Hmem.
  all: match goal with Hm : controlled_mono _ _ |- _ => apply Hm end;
    unfold R.observe; destruct (Ranks.observe (R.ranking st) _) as [order rank];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; exact Hmem.
Qed.
Lemma steps_controlled_mono tf before after : steps tf before after -> controlled_mono (R.cfg_state before) (R.cfg_state after).
Proof. intro H; induction H; intros owner Hmem; auto; apply IHsteps; eapply next_controlled_mono; eauto. Qed.

(** An uncontrolled value is read only by lower owners. Consequently its
    direct assignment cannot create work at or above its own rank. *)
Definition forward_readers st := forall target reader,
  S.mem reader (R.lookup_set (R.readers st) target) = true ->
  S.mem target (R.controlled st) = true \/ R.rank_lt st reader target = true.
Lemma forward_readers_layout before after :
  R.readers after = R.readers before -> controlled_mono before after ->
  extends (R.ranking before) (R.ranking after) -> forward_readers before -> forward_readers after.
Proof.
  intros Hr Hc He H target reader Hmem; rewrite Hr in Hmem;
    destruct (H target reader Hmem); [left; apply Hc; assumption |right; eapply lt_extends; eauto].
Qed.
Lemma forward_readers_get st fr target next next_fr value :
  R.complete_get st fr target = (next,next_fr,value) -> forward_readers st -> forward_readers next.
Proof.
  intros Hget Hreaders; unfold R.complete_get in Hget.
  destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hhigher;
    inversion Hget; subst next next_fr value; clear Hget;
    unfold R.materialize; destruct (M.lookup _ target); intros observed reader Hmem;
    cbn [R.with_sigma R.with_readers R.with_controlled R.promote_controlled R.readers R.controlled R.ranking R.rank_lt] in *;
    unfold R.lookup_set in Hmem; destruct (V.eq_dec observed target) as [-> |Hneq].
  all: try rewrite ML.lookup_update_same in Hmem;
    try rewrite ML.lookup_update_other in Hmem by assumption.
  all: cbn [R.rank_lt R.ranking R.with_readers R.with_sigma R.promote_controlled R.with_controlled].
  all: try solve [apply SL.add_spec in Hmem; destruct Hmem as [-> |Hmem];
    [right; exact Hhigher |exact (Hreaders target reader Hmem)]].
  all: try solve [left; apply SL.add_spec; auto].
  all: change (S.mem reader (R.lookup_set (R.readers st) observed) = true) in Hmem;
    destruct (Hreaders observed reader Hmem) as [Hcontrolled |Hlt];
    [left; try exact Hcontrolled; apply SL.add_spec; auto |right; exact Hlt].
Qed.
Lemma forward_readers_write st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) -> forward_readers st -> forward_readers next.
Proof.
  intros Hwrite H; destruct (write_layout Hwrite) as [Hr [_ [_ [Hreaders _]]]].
  eapply forward_readers_layout with (before := st);
    [exact Hreaders |eapply controlled_write; exact Hwrite |rewrite Hr; apply extends_refl |exact H].
Qed.
Lemma forward_readers_commit st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) -> forward_readers st -> forward_readers next.
Proof.
  intros Hset H; unfold R.set_value in Hset; split_program Hset; try exact H.
  all: intros target reader Hmem; cbn [R.with_readers R.with_queue R.with_sigma R.readers R.controlled R.ranking R.rank_lt] in *;
    unfold R.lookup_set in Hmem; destruct (V.eq_dec target (R.frame_owner fr)) as [-> |Hneq].
  all: try solve [rewrite ML.lookup_update_same in Hmem; rewrite SL.empty_spec in Hmem; discriminate].
  all: rewrite ML.lookup_update_other in Hmem by assumption;
    apply H; exact Hmem.
Qed.
Arguments forward_readers_commit {st fr direct next next_fr} _ _.
Lemma forward_readers_observe st target : forward_readers st -> forward_readers (R.observe st target).
Proof.
  intro H; eapply forward_readers_layout with (before := st);
    [unfold R.observe; destruct (Ranks.observe (R.ranking st) target); reflexivity
    |apply controlled_layout; unfold R.observe; destruct (Ranks.observe (R.ranking st) target); reflexivity
    |apply observe_extends |exact H].
Qed.
Theorem next_forward_readers tf before after : forward_readers (R.cfg_state before) ->
  step tf before after -> forward_readers (R.cfg_state after).
Proof.
  intros Hreaders Hstep; destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep, Hreaders.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead in Hstep; split_program Hstep.
  all: repeat match goal with
  | Hget : R.complete_get _ _ _ = (_,_,_) |- _ =>
      let Hf := fresh "get_forward" in pose proof (forward_readers_get Hget) as Hf; clear Hget
  | Hwrite : R.write_side_contribution _ _ _ _ = (_,_) |- _ =>
      let Hf := fresh "write_forward" in pose proof (forward_readers_write Hwrite) as Hf; clear Hwrite
  | Hset : R.set_value _ _ _ = (_,_) |- _ =>
      let Hf := fresh "commit_forward" in pose proof (forward_readers_commit Hset) as Hf; clear Hset
  end.
  all: cbn [R.cfg_state] in *;
    try solve [eapply forward_readers_layout with (before := st); [reflexivity |apply controlled_layout; reflexivity |apply extends_refl |exact Hreaders]].
  all: try solve [match goal with Hf : forward_readers _ -> forward_readers _ |- _ => apply Hf end;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    try exact Hreaders; apply forward_readers_observe; exact Hreaders].
  all: unfold R.materialize, R.reset_registered_cells;
    repeat match goal with
    | |- context [match M.lookup ?table ?target with _ => _ end] => destruct (M.lookup table target)
    | |- context [if ?b then _ else _] => destruct b
    end.
  all: eapply forward_readers_layout with (before := st);
      [unfold R.observe; try destruct (Ranks.observe (R.ranking st) _); reflexivity
      |apply controlled_layout; unfold R.observe; try destruct (Ranks.observe (R.ranking st) _); reflexivity
      |try apply observe_extends; try apply extends_refl
      |exact Hreaders].
Qed.
Theorem reachable_forward_readers tf roots c : steps tf (R.initial_config roots) c -> forward_readers (R.cfg_state c).
Proof.
  intro Hpath; assert (Hinitial : forward_readers (R.cfg_state (R.initial_config roots))).
  { intros target reader Hmem; unfold R.lookup_set in Hmem; cbn in Hmem;
    rewrite ML.lookup_empty, SL.empty_spec in Hmem; discriminate. }
  revert Hinitial; induction Hpath; auto; intro Hfirst; apply IHHpath; eapply next_forward_readers; eauto.
Qed.

Definition configuration st ctrl : R.config := {| R.cfg_state := st; R.cfg_control := ctrl |}.
Definition reachable tf roots c := steps tf (R.initial_config roots) c.
Definition queue_below st owner := Forall (fun x => R.rank_lt st x owner = true) (R.queue st).
Definition episode_complete tf start owner k := exists final,
  steps tf start (configuration final (R.Return k)) /\ queue_below final owner.
Lemma reachable_advance tf roots before after : reachable tf roots before -> step tf before after -> reachable tf roots after.
Proof. intros Hpath Hstep; eapply steps_snoc; eauto. Qed.
Lemma reachable_follow tf roots before after : reachable tf roots before -> steps tf before after -> reachable tf roots after.
Proof. intros Hpath Htail; eapply steps_append; eauto. Qed.

Section Evaluation.
Variable tf : Syntax.system.
Variable roots : list V.t.
Variable owner : V.t.
Hypothesis higher_episodes : forall st child k,
  reachable tf roots (configuration st (R.StartEpisode child k)) -> R.rank_lt st owner child = true ->
  episode_complete tf (configuration st (R.StartEpisode child k)) child k.

(** The structural induction visits each residual constraint once. A recursive
    call invokes only the hypothesis for a strictly higher owner. *)
Lemma dead_reaches_commit pending st fr direct k : R.frame_owner fr = owner ->
  reachable tf roots (configuration st (R.RunDead fr direct pending k)) ->
  exists final, steps tf (configuration st (R.RunDead fr direct pending k))
    (configuration final (R.RunCommit fr direct k)).
Proof.
  revert st; induction pending as [|target pending IH]; intros st Howner Hreachable.
  - exists (R.publish_targets st fr); apply steps_cons with (next := configuration (R.publish_targets st fr) (R.RunCommit fr direct k));
      [reflexivity |constructor].
  - destruct (S.mem target (R.frame_current_targets fr)) eqn:Hmem.
    + assert (Hstep : step tf (configuration st (R.RunDead fr direct (target :: pending) k))
        (configuration st (R.RunDead fr direct pending k))) by (unfold step, configuration; cbn; rewrite Hmem; reflexivity).
      destruct (IH st Howner (reachable_advance Hreachable Hstep)) as [final Htail].
      exists final; eapply steps_cons; eauto.
    + destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite.
      assert (Hstep : step tf (configuration st (R.RunDead fr direct (target :: pending) k))
        (R.continue_dead next fr direct target pending k changed)).
      { unfold step, configuration; cbn -[R.write_side_contribution]; rewrite Hmem, Hwrite; reflexivity. }
      pose proof (reachable_advance Hreachable Hstep) as Hnext.
      unfold R.continue_dead in Hstep, Hnext.
      destruct changed; [destruct (R.rank_lt next (R.frame_owner fr) target && negb (R.is_materialized next target)) eqn:Hchild |].
      * apply andb_true_iff in Hchild; destruct Hchild as [Hhigher _]; rewrite Howner in Hhigher.
        destruct (higher_episodes Hnext Hhigher) as [returned [Hepisode Hbelow]].
        assert (Hresume : step tf (configuration returned (R.Return (R.KDead fr direct pending k)))
          (configuration returned (R.RunDead fr direct pending k))) by reflexivity.
        destruct (IH returned Howner (reachable_advance (reachable_follow Hnext Hepisode) Hresume)) as [final Htail].
        exists final; eapply steps_cons; [exact Hstep |].
        eapply steps_append; [exact Hepisode |eapply steps_cons; eauto].
      * destruct (IH (R.enqueue next target) Howner Hnext) as [final Htail]; exists final; eapply steps_cons; eauto.
      * destruct (IH next Howner Hnext) as [final Htail]; exists final; eapply steps_cons; eauto.
Qed.

Lemma rhs_reaches_commit body st fr k : R.frame_owner fr = owner ->
  reachable tf roots (configuration st (R.RunRhs fr body k)) ->
  exists final final_fr direct, R.frame_owner final_fr = owner /\
    steps tf (configuration st (R.RunRhs fr body k)) (configuration final (R.RunCommit final_fr direct k)).
Proof.
  revert st fr k; induction body as [direct|target tail IH|target raw tail IH|target tail IH]; intros st fr k Howner Hreachable.
  - set (pending := if Features.eliminate_dead_sides then S.elements (R.frame_previous_targets fr) else []).
    assert (Hstep : step tf (configuration st (R.RunRhs fr (Syntax.Ret direct) k))
      (configuration st (R.RunDead fr direct pending k))) by reflexivity.
    destruct (dead_reaches_commit Howner (reachable_advance Hreachable Hstep)) as [final Htail].
    exists final, fr, direct; split; [exact Howner |eapply steps_cons; eauto].
  - set (observed := R.observe st target).
    destruct (negb (R.is_materialized observed target) && R.rank_lt observed (R.frame_owner fr) target) eqn:Hchild.
    + assert (Hstep : step tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k))
        (configuration observed (R.StartEpisode target (R.KAfterGet fr target tail k)))).
      { unfold step, configuration; cbn -[R.observe R.complete_get]; fold observed; rewrite Hchild; reflexivity. }
      pose proof (reachable_advance Hreachable Hstep) as Hnext.
      apply andb_true_iff in Hchild; destruct Hchild as [_ Hhigher]; rewrite Howner in Hhigher.
      destruct (higher_episodes Hnext Hhigher) as [returned [Hepisode Hbelow]].
      destruct (R.complete_get returned fr target) as [[next next_fr] value] eqn:Hget.
      assert (Hresume : step tf (configuration returned (R.Return (R.KAfterGet fr target tail k)))
        (configuration next (R.RunRhs next_fr (tail value) k))).
      { unfold step, configuration; cbn -[R.complete_get]; rewrite Hget; reflexivity. }
      assert (Hnext_owner : R.frame_owner next_fr = owner) by (rewrite (get_owner Hget); exact Howner).
      destruct (IH value next next_fr k Hnext_owner (reachable_advance (reachable_follow Hnext Hepisode) Hresume))
        as [final [final_fr [direct [Hfinal Htail]]]].
      exists final, final_fr, direct; split; [exact Hfinal |eapply steps_cons; [exact Hstep |]].
      eapply steps_append; [exact Hepisode |eapply steps_cons; eauto].
    + set (base := if R.is_materialized observed target then observed else R.enqueue observed target).
      destruct (R.complete_get base fr target) as [[next next_fr] value] eqn:Hget.
      assert (Hstep : step tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k))
        (configuration next (R.RunRhs next_fr (tail value) k))).
      { unfold step, configuration; cbn -[R.observe R.complete_get]; fold observed; rewrite Hchild; fold base; rewrite Hget; reflexivity. }
      assert (Hnext_owner : R.frame_owner next_fr = owner) by (rewrite (get_owner Hget); exact Howner).
      destruct (IH value next next_fr k Hnext_owner (reachable_advance Hreachable Hstep))
        as [final [final_fr [direct [Hfinal Htail]]]].
      exists final, final_fr, direct; split; [exact Hfinal |eapply steps_cons; eauto].
  - set (input := R.accumulated_side_input fr target raw).
    set (next_fr := R.with_frame_side fr target input).
    destruct (R.write_side_contribution (R.observe st target) next_fr target input) as [next changed] eqn:Hwrite.
    assert (Hstep : step tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k))
      (R.continue_side next next_fr target tail k changed)).
    { unfold step, configuration; cbn -[R.observe R.write_side_contribution]; fold input; fold next_fr; rewrite Hwrite; reflexivity. }
    assert (Hnext_owner : R.frame_owner next_fr = owner) by (exact Howner).
    pose proof (reachable_advance Hreachable Hstep) as Hnext.
    unfold R.continue_side in Hstep, Hnext.
    destruct changed; [destruct (R.rank_lt next (R.frame_owner next_fr) target && negb (R.is_materialized next target)) eqn:Hchild |].
    + apply andb_true_iff in Hchild; destruct Hchild as [Hhigher _]; rewrite Hnext_owner in Hhigher.
      destruct (higher_episodes Hnext Hhigher) as [returned [Hepisode Hbelow]].
      assert (Hresume : step tf (configuration returned (R.Return (R.KAfterSide next_fr tail k)))
        (configuration returned (R.RunRhs next_fr tail k))) by reflexivity.
      destruct (IH returned next_fr k Hnext_owner (reachable_advance (reachable_follow Hnext Hepisode) Hresume))
        as [final [final_fr [direct [Hfinal Htail]]]].
      exists final, final_fr, direct; split; [exact Hfinal |eapply steps_cons; [exact Hstep |]].
      eapply steps_append; [exact Hepisode |eapply steps_cons; eauto].
    + destruct (IH (R.enqueue next target) next_fr k Hnext_owner Hnext) as [final [final_fr [direct [Hfinal Htail]]]].
      exists final, final_fr, direct; split; [exact Hfinal |eapply steps_cons; eauto].
    + destruct (IH next next_fr k Hnext_owner Hnext) as [final [final_fr [direct [Hfinal Htail]]]].
      exists final, final_fr, direct; split; [exact Hfinal |eapply steps_cons; eauto].
  - set (observed := R.observe st target).
    destruct (R.is_materialized observed target) eqn:Hmat.
    + assert (Hstep : step tf (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k))
        (configuration observed (R.RunRhs fr tail k))).
      { unfold step, configuration; cbn -[R.observe]; fold observed; rewrite Hmat; reflexivity. }
      destruct (IH observed fr k Howner (reachable_advance Hreachable Hstep)) as [final [final_fr [direct [Hfinal Htail]]]].
      exists final, final_fr, direct; split; [exact Hfinal |eapply steps_cons; eauto].
    + destruct (R.rank_lt observed (R.frame_owner fr) target) eqn:Hhigher.
      * assert (Hstep : step tf (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k))
          (configuration observed (R.StartEpisode target (R.KAfterSpawn fr tail k)))).
        { unfold step, configuration; cbn -[R.observe]; fold observed; rewrite Hmat, Hhigher; reflexivity. }
        pose proof (reachable_advance Hreachable Hstep) as Hnext; rewrite Howner in Hhigher.
        destruct (higher_episodes Hnext Hhigher) as [returned [Hepisode Hbelow]].
        assert (Hresume : step tf (configuration returned (R.Return (R.KAfterSpawn fr tail k)))
          (configuration returned (R.RunRhs fr tail k))) by reflexivity.
        destruct (IH returned fr k Howner (reachable_advance (reachable_follow Hnext Hepisode) Hresume))
          as [final [final_fr [direct [Hfinal Htail]]]].
        exists final, final_fr, direct; split; [exact Hfinal |eapply steps_cons; [exact Hstep |]].
        eapply steps_append; [exact Hepisode |eapply steps_cons; eauto].
      * assert (Hstep : step tf (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k))
          (configuration (R.materialize (R.enqueue observed target) target) (R.RunRhs fr tail k))).
        { unfold step, configuration; cbn -[R.observe]; fold observed; rewrite Hmat, Hhigher; reflexivity. }
        destruct (IH (R.materialize (R.enqueue observed target) target) fr k Howner (reachable_advance Hreachable Hstep))
          as [final [final_fr [direct [Hfinal Htail]]]].
        exists final, final_fr, direct; split; [exact Hfinal |eapply steps_cons; eauto].
Qed.
End Evaluation.

Lemma steps_ranking_extends tf before after : steps tf before after ->
  extends (R.ranking (R.cfg_state before)) (R.ranking (R.cfg_state after)).
Proof. intro H; induction H; [apply extends_refl |eapply extends_trans; [eapply next_ranking_extends; exact H |exact IHsteps]]. Qed.
Definition queue_ceiling st ceiling := forall x, In x (R.queue st) ->
  exists rank, Ranks.lookup (R.ranking st) x = Some rank /\ rank < ceiling.
Definition drain_boundary tf owner phase k c :=
  queue_below (R.cfg_state c) owner /\
  (R.cfg_control c = R.Return k \/ exists fr,
    R.cfg_control c = R.RunRhs fr (tf owner) k /\ R.frame_owner fr = owner /\ R.frame_phase fr = phase).
Lemma queue_below_close st child owner : queue_below st owner -> queue_below (R.reset_registered_cells st child) owner.
Proof.
  unfold queue_below; rewrite close_queue; unfold R.rank_lt; rewrite close_rank; auto.
Qed.
Lemma queue_below_ceiling st owner rank : queue_below st owner ->
  Ranks.lookup (R.ranking st) owner = Some rank -> queue_ceiling st rank.
Proof.
  intros Hbelow Hrank x Hin; unfold queue_below in Hbelow; rewrite Forall_forall in Hbelow;
    destruct (@lt_ranks (R.ranking st) x owner (Hbelow x Hin)) as [rx [ry [Hx [Hy Hlt]]]];
    rewrite Hrank in Hy; inversion Hy; subst; eauto.
Qed.

Section Draining.
Variable tf : Syntax.system.
Variable roots : list V.t.
Variable owner : V.t.
Hypothesis higher_episodes : forall st child k,
  reachable tf roots (configuration st (R.StartEpisode child k)) -> R.rank_lt st owner child = true ->
  episode_complete tf (configuration st (R.StartEpisode child k)) child k.
Lemma drain_reaches_boundary ceiling st fr k : R.frame_owner fr = owner ->
  reachable tf roots (configuration st (R.RunDrain fr k)) -> queue_ceiling st ceiling ->
  exists final, steps tf (configuration st (R.RunDrain fr k)) final /\
    drain_boundary tf owner (R.frame_phase fr) k final.
Proof.
  revert st fr k; induction ceiling using lt_wf_ind; intros st fr k Howner Hreachable Hceiling.
  pose proof (@reachable_rank_configuration tf roots (configuration st (R.RunDrain fr k)) Hreachable) as [Hstore Hrefs].
  cbn [configuration R.cfg_state R.cfg_control control_refs] in Hstore, Hrefs; destruct Hrefs as [Hfr Hk].
  assert (Howner_ranked : ranked (R.ranking st) owner) by (rewrite <- Howner; exact (proj2 (ref_owner Hfr))).
  destruct (R.queue st) as [|head rest] eqn:Hqueue.
  - exists (configuration (R.reset_registered_cells st owner) (R.Return k)); split.
    + apply steps_cons with (next := configuration (R.reset_registered_cells st owner) (R.Return k)); [|constructor].
      unfold step, configuration; cbn -[R.reset_registered_cells]; rewrite Hqueue; cbn; now rewrite Howner.
    + split; [apply queue_below_close; unfold queue_below; rewrite Hqueue; constructor |left; reflexivity].
  - destruct (V.eq_dec head owner) as [-> |Hneq].
    + exists (configuration (R.with_queue st rest)
        (R.RunRhs (R.fresh_frame (R.with_queue st rest) owner (R.frame_phase fr)) (tf owner) k)); split.
      * apply steps_cons with (next := configuration (R.with_queue st rest)
          (R.RunRhs (R.fresh_frame (R.with_queue st rest) owner (R.frame_phase fr)) (tf owner) k)); [|constructor].
        unfold step, configuration; cbn -[R.fresh_frame]; rewrite Hqueue, Howner; cbn;
          destruct (V.eq_dec owner owner); [reflexivity |contradiction].
      * split.
        -- unfold queue_below; cbn [R.with_queue R.queue R.rank_lt R.ranking];
             pose proof (proj2 (@ordered_tail (R.ranking st) owner rest ltac:(rewrite <- Hqueue; exact (store_ordered Hstore)))) as Hbelow;
             exact Hbelow.
        -- right; eexists; repeat split; reflexivity.
    + destruct (R.rank_lt st owner head) eqn:Hhigher.
      * assert (Hstep : step tf (configuration st (R.RunDrain fr k))
          (configuration (R.with_queue st rest) (R.StartEpisode head (R.KDrain fr k)))).
        { unfold step, configuration; cbn -[R.rank_lt]; rewrite Hqueue, Howner; cbn;
            destruct (V.eq_dec head owner); [contradiction |rewrite Hhigher; reflexivity]. }
        pose proof (reachable_advance Hreachable Hstep) as Hnext.
        destruct (higher_episodes Hnext Hhigher) as [returned [Hepisode Hbelow]].
        destruct (Hceiling head ltac:(rewrite Hqueue; left; reflexivity)) as [rank [Hrank Hbound]].
        assert (Hreturned_rank : Ranks.lookup (R.ranking returned) head = Some rank).
        { exact (steps_ranking_extends Hepisode Hrank). }
        assert (Hresume : step tf (configuration returned (R.Return (R.KDrain fr k)))
          (configuration returned (R.RunDrain fr k))) by reflexivity.
        destruct (H rank Hbound returned fr k Howner
          (reachable_advance (reachable_follow Hnext Hepisode) Hresume)
          (queue_below_ceiling Hbelow Hreturned_rank)) as [final [Htail Hboundary]].
        exists final; split; [eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hepisode |eapply steps_cons; eauto]] |exact Hboundary].
      * assert (Hlower : R.rank_lt st head owner = true).
        { assert (Hhead : ranked (R.ranking st) head).
          { pose proof (known_ranked_queue Hstore) as Hq; rewrite Hqueue in Hq; inversion Hq; assumption. }
          destruct (@lt_compare (R.ranking st) head owner (store_valid Hstore) Hhead
            Howner_ranked Hneq) as [Hlt |Hlt]; [exact Hlt |unfold R.rank_lt in Hhigher; congruence]. }
        assert (Hbelow : queue_below st owner).
        { unfold queue_below; rewrite Hqueue; constructor; [exact Hlower |].
          destruct (@ordered_tail (R.ranking st) head rest ltac:(rewrite <- Hqueue; exact (store_ordered Hstore))) as [_ Htail].
          rewrite Forall_forall in *; intros x Hin; eapply lt_trans; [apply Htail; exact Hin |exact Hlower]. }
        exists (configuration (R.reset_registered_cells st owner) (R.Return k)); split.
        -- apply steps_cons with (next := configuration (R.reset_registered_cells st owner) (R.Return k)); [|constructor].
           unfold step, configuration; cbn -[R.reset_registered_cells R.rank_lt]; rewrite Hqueue, Howner; cbn;
             destruct (V.eq_dec head owner); [contradiction |rewrite Hhigher; reflexivity].
        -- split; [apply queue_below_close; exact Hbelow |left; reflexivity].
Qed.
End Draining.

Theorem finite_queue_ceiling tf roots (finite : Sem.finite_system tf roots) st ctrl :
  reachable tf roots (configuration st ctrl) -> queue_ceiling st (RF.bound (Sem.support finite)).
Proof.
  intros Hreachable owner Hin.
  pose proof (@reachable_configuration_wf tf roots finite (configuration st ctrl) Hreachable) as [Hstore _].
  cbn [configuration R.cfg_state] in Hstore;
  pose proof (known_ranked_queue Hstore) as Hranked; rewrite Forall_forall in Hranked;
    destruct (Hranked owner Hin) as [rank Hrank]; exists rank; split; [exact Hrank |].
  eapply reachable_rank_bound; [exact Hreachable |exact Hrank].
Qed.

Lemma materialized_iff_solved st x : R.is_materialized st x = true <-> solved st x.
Proof.
  split; [apply materialized_solved |intros [value Hvalue]; unfold Store.sigma in Hvalue; unfold R.is_materialized; rewrite Hvalue; reflexivity].
Qed.
Definition missing_count support st := sum_over (fun x => if R.is_materialized st x then 0 else 1) support.
Lemma missing_count_mono support before after : preserves_live before after -> missing_count support after <= missing_count support before.
Proof.
  intro Hlive; apply sum_over_le; intros x Hin.
  destruct (R.is_materialized before x) eqn:Hbefore; destruct (R.is_materialized after x) eqn:Hafter; try lia.
  apply materialized_iff_solved in Hbefore; apply Hlive in Hbefore; apply materialized_iff_solved in Hbefore; congruence.
Qed.
Lemma missing_count_strict support before after x : preserves_live before after -> In x support ->
  R.is_materialized before x = false -> solved after x -> missing_count support after < missing_count support before.
Proof.
  intros Hlive Hin Hmissing Hsolved; apply materialized_iff_solved in Hsolved.
  eapply sum_over_lt with (x := x); [exact Hin |rewrite Hmissing, Hsolved; cbn; lia |].
  intros y Hy; destruct (R.is_materialized before y) eqn:Hbefore; destruct (R.is_materialized after y) eqn:Hafter; try lia.
  apply materialized_iff_solved in Hbefore; apply Hlive in Hbefore; apply materialized_iff_solved in Hbefore; congruence.
Qed.
Definition promotion_reserve st owner := if S.mem owner (R.controlled st) then 0 else 1.
Definition owner_credit support st owner phase := incident_credit support st owner +
  if S.mem owner (R.controlled st) then UL.remaining_changes phase (R.sigma_value st owner) else 0.
Definition round_budget support st owner phase :=
  (missing_count support st, (promotion_reserve st owner, owner_credit support st owner phase)).
Definition budget_lt := Relation_Operators.slexprod nat (nat * nat) lt
  (Relation_Operators.slexprod nat nat lt lt).
Definition budget_le (next previous : nat * (nat * nat)) := next = previous \/ budget_lt next previous.
Definition round_order support owner (next previous : nat * (R.state * U.phase)) :=
  Relation_Operators.slexprod nat (nat * (nat * nat)) lt budget_lt
    (fst next, round_budget support (fst (snd next)) owner (snd (snd next)))
    (fst previous, round_budget support (fst (snd previous)) owner (snd (snd previous))).
Lemma round_order_well_founded support owner : well_founded (round_order support owner).
Proof.
  unfold round_order; apply wf_inverse_image; repeat apply wf_slexprod; apply Nat.lt_wf_0.
Qed.
Lemma budget_components a b c a' b' c' : a' <= a -> b' <= b -> c' <= c ->
  budget_le (a',(b',c')) (a,(b,c)).
Proof.
  intros Ha Hb Hc; unfold budget_le, budget_lt.
  destruct (proj1 (Nat.lt_eq_cases _ _) Ha) as [Hlt | ->]; [right; apply Relation_Operators.left_slex; exact Hlt |].
  destruct (proj1 (Nat.lt_eq_cases _ _) Hb) as [Hlt | ->]; [right; apply Relation_Operators.right_slex, Relation_Operators.left_slex; exact Hlt |].
  destruct (proj1 (Nat.lt_eq_cases _ _) Hc) as [Hlt | ->]; [right; repeat apply Relation_Operators.right_slex; exact Hlt |left; reflexivity].
Qed.
Lemma budget_components_strict a b c a' b' c' : a' <= a -> b' <= b -> c' < c ->
  budget_lt (a',(b',c')) (a,(b,c)).
Proof.
  intros Ha Hb Hc; unfold budget_lt.
  destruct (proj1 (Nat.lt_eq_cases _ _) Ha) as [Hlt | ->]; [apply Relation_Operators.left_slex; exact Hlt |].
  destruct (proj1 (Nat.lt_eq_cases _ _) Hb) as [Hlt | ->]; [apply Relation_Operators.right_slex, Relation_Operators.left_slex; exact Hlt |].
  repeat apply Relation_Operators.right_slex; exact Hc.
Qed.
Lemma budget_growth support before after owner phase next_phase :
  preserves_live before after -> controlled_mono before after ->
  incident_credit support after owner <= incident_credit support before owner ->
  (S.mem owner (R.controlled before) = true ->
    UL.remaining_changes next_phase (R.sigma_value after owner) <= UL.remaining_changes phase (R.sigma_value before owner)) ->
  budget_le (round_budget support after owner next_phase) (round_budget support before owner phase).
Proof.
  intros Hl Hc Hside Hordinary; pose proof (missing_count_mono support Hl) as Hmissing.
  unfold round_budget, promotion_reserve, owner_credit.
  destruct (S.mem owner (R.controlled before)) eqn:Hbefore;
    destruct (S.mem owner (R.controlled after)) eqn:Hafter; cbn.
  - apply budget_components; try lia; pose proof (Hordinary eq_refl); lia.
  - pose proof (Hc owner Hbefore); congruence.
  - unfold budget_le, budget_lt; right.
    destruct (proj1 (Nat.lt_eq_cases _ _) Hmissing) as [Hlt |Heq]; [apply Relation_Operators.left_slex; exact Hlt |].
    rewrite Heq; apply Relation_Operators.right_slex, Relation_Operators.left_slex; lia.
  - apply budget_components; lia.
Qed.
Lemma budget_side_strict support before after owner phase next_phase :
  preserves_live before after -> controlled_mono before after ->
  incident_credit support after owner < incident_credit support before owner ->
  (S.mem owner (R.controlled before) = true ->
    UL.remaining_changes next_phase (R.sigma_value after owner) <= UL.remaining_changes phase (R.sigma_value before owner)) ->
  budget_lt (round_budget support after owner next_phase) (round_budget support before owner phase).
Proof.
  intros Hl Hc Hside Hordinary; pose proof (missing_count_mono support Hl) as Hmissing.
  unfold round_budget, promotion_reserve, owner_credit.
  destruct (S.mem owner (R.controlled before)) eqn:Hbefore;
    destruct (S.mem owner (R.controlled after)) eqn:Hafter; cbn.
  - apply budget_components_strict; try lia; pose proof (Hordinary eq_refl); lia.
  - pose proof (Hc owner Hbefore); congruence.
  - unfold budget_lt; destruct (proj1 (Nat.lt_eq_cases _ _) Hmissing) as [Hlt |Heq];
      [apply Relation_Operators.left_slex; exact Hlt |rewrite Heq; apply Relation_Operators.right_slex, Relation_Operators.left_slex; lia].
  - apply budget_components_strict; lia.
Qed.
Lemma incident_credit_layout support before after owner : R.side_cells after = R.side_cells before ->
  R.contributions after = R.contributions before -> incident_credit support after owner = incident_credit support before owner.
Proof.
  intros Hcells Hcontrib; unfold incident_credit; f_equal;
    induction support as [|head rest IH]; cbn; try reflexivity;
    rewrite (@side_credit_layout before after _ _ Hcells Hcontrib), IH; reflexivity.
Qed.
Lemma budget_commit support st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  budget_le (round_budget support next (R.frame_owner fr) (R.frame_phase next_fr))
    (round_budget support st (R.frame_owner fr) (R.frame_phase fr)).
Proof.
  intro Hset; pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview.
  apply budget_growth; [eapply preserves_live_commit; exact Hset |eapply controlled_commit; exact Hset | |].
  - rewrite (@incident_credit_layout support st next (R.frame_owner fr) (commit_cells Hview) (commit_contributions Hview)); lia.
  - intro Hcontrolled; eapply commit_credit; eauto.
Qed.
Lemma budget_commit_changed support st fr direct next next_fr : S.mem (R.frame_owner fr) (R.controlled st) = true ->
  R.set_value st fr direct = (next,next_fr) ->
  R.equivalent (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) = false ->
  budget_lt (round_budget support next (R.frame_owner fr) (R.frame_phase next_fr))
    (round_budget support st (R.frame_owner fr) (R.frame_phase fr)).
Proof.
  intros Hcontrolled Hset Hchanged; pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview.
  pose proof (@commit_credit_strict st fr direct next next_fr Hcontrolled Hset Hchanged) as Hcredit.
  unfold round_budget, promotion_reserve, owner_credit; rewrite (commit_controlled Hview), Hcontrolled;
    cbn; apply budget_components_strict.
  - apply missing_count_mono; eapply preserves_live_commit; exact Hset.
  - lia.
  - rewrite (@incident_credit_layout support st next (R.frame_owner fr) (commit_cells Hview) (commit_contributions Hview)); lia.
Qed.
Lemma budget_write support st fr target input next changed owner phase :
  R.write_side_contribution st fr target input = (next,changed) ->
  budget_le (round_budget support next owner phase) (round_budget support st owner phase).
Proof.
  intro Hwrite; pose proof (write_layout Hwrite) as [_ [_ [Hsigma _]]].
  apply budget_growth.
  - apply preserves_live_layout; exact Hsigma.
  - eapply controlled_write; exact Hwrite.
  - eapply incident_credit_write; exact Hwrite.
  - intro Hcontrolled; unfold R.sigma_value; rewrite Hsigma; lia.
Qed.
Lemma budget_write_changed support st fr target input next owner phase :
  R.write_side_contribution st fr target input = (next,true) -> In (R.frame_owner fr) support -> In target support ->
  (owner = R.frame_owner fr \/ owner = target) ->
  budget_lt (round_budget support next owner phase) (round_budget support st owner phase).
Proof.
  intros Hwrite Hsource Htarget Hincident; pose proof (write_layout Hwrite) as [_ [_ [Hsigma _]]].
  apply budget_side_strict.
  - apply preserves_live_layout; exact Hsigma.
  - eapply controlled_write; exact Hwrite.
  - eapply incident_credit_write_strict; eauto.
  - intro Hcontrolled; unfold R.sigma_value; rewrite Hsigma; lia.
Qed.
Lemma budget_higher_close support st owner child phase : reset_scoped st -> R.rank_lt st owner child = true ->
  round_budget support (R.reset_registered_cells st child) owner phase = round_budget support st owner phase.
Proof.
  intros Hreset Hhigher; unfold round_budget, owner_credit;
    rewrite (@incident_credit_higher_close support st owner child Hreset Hhigher).
  unfold missing_count, promotion_reserve, R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity.
Qed.

(** A whole round reaches either episode return or a fresh RHS evaluation.
    Only the latter still needs the decreasing-round argument. *)
Theorem round_reaches_boundary tf roots (finite : Sem.finite_system tf roots) owner st fr k :
  (forall st child k, reachable tf roots (configuration st (R.StartEpisode child k)) ->
    R.rank_lt st owner child = true -> episode_complete tf (configuration st (R.StartEpisode child k)) child k) ->
  R.frame_owner fr = owner -> reachable tf roots (configuration st (R.RunRhs fr (tf owner) k)) ->
  exists final phase, steps tf (configuration st (R.RunRhs fr (tf owner) k)) final /\ drain_boundary tf owner phase k final.
Proof.
  intros Hchildren Howner Hreachable.
  destruct (@rhs_reaches_commit tf roots owner Hchildren (tf owner) st fr k Howner Hreachable)
    as [committed [commit_fr [direct [Hcommit_owner Heval]]]].
  pose proof (reachable_follow Hreachable Heval) as Hcommit.
  destruct (R.set_value committed commit_fr direct) as [drained drain_fr] eqn:Hset.
  set (next := R.requeue_changed_controlled_owner committed drained (R.frame_owner commit_fr)).
  assert (Hstep : step tf (configuration committed (R.RunCommit commit_fr direct k)) (configuration next (R.RunDrain drain_fr k))).
  { unfold step, configuration; cbn -[R.set_value]; rewrite Hset; reflexivity. }
  pose proof (reachable_advance Hcommit Hstep) as Hdrain.
  assert (Hframe : R.frame_owner drain_fr = owner).
  { rewrite (commit_owner (@commit_footprint committed commit_fr direct drained drain_fr Hset)); exact Hcommit_owner. }
  destruct (@drain_reaches_boundary tf roots owner Hchildren (RF.bound (Sem.support finite)) next drain_fr k
    Hframe Hdrain (@finite_queue_ceiling tf roots finite next (R.RunDrain drain_fr k) Hdrain))
    as [final [Hdraining Hboundary]].
  exists final, (R.frame_phase drain_fr); split; [eapply steps_append; [exact Heval |eapply steps_cons; eauto] |exact Hboundary].
Qed.

Lemma insert_lower order owner x queue : R.ranking_lt order x owner = true ->
  Forall (fun y => R.ranking_lt order y owner = true) queue ->
  Forall (fun y => R.ranking_lt order y owner = true) (R.queue_insert order x queue).
Proof.
  intros Hx Hq; rewrite Forall_forall in *; intros y Hin; apply insert_members in Hin;
    destruct Hin as [-> |Hin]; auto.
Qed.
Lemma insert_all_lower order owner xs queue :
  Forall (fun y => R.ranking_lt order y owner = true) xs ->
  Forall (fun y => R.ranking_lt order y owner = true) queue ->
  Forall (fun y => R.ranking_lt order y owner = true) (R.queue_insert_all order xs queue).
Proof.
  intro Hxs; revert queue; induction Hxs; cbn; intros queue Hq; auto;
    apply IHHxs, insert_lower; auto.
Qed.
Lemma uncontrolled_readers_lower st owner : forward_readers st -> S.mem owner (R.controlled st) = false ->
  Forall (fun reader => R.rank_lt st reader owner = true) (S.elements (R.lookup_set (R.readers st) owner)).
Proof.
  intros Hforward Howner; apply Forall_forall; intros reader Hin; apply SL.mem_spec in Hin;
    destruct (Hforward owner reader Hin); congruence.
Qed.
Theorem uncontrolled_commit_keeps_lower_queue st fr direct next next_fr :
  forward_readers st -> S.mem (R.frame_owner fr) (R.controlled st) = false -> queue_below st (R.frame_owner fr) ->
  R.set_value st fr direct = (next,next_fr) ->
  queue_below (R.requeue_changed_controlled_owner st next (R.frame_owner fr)) (R.frame_owner fr).
Proof.
  intros Hforward Hcontrolled Hbelow Hset.
  assert (Hreaders := uncontrolled_readers_lower Hforward Hcontrolled).
  unfold R.requeue_changed_controlled_owner; rewrite Hcontrolled, andb_false_r; cbn.
  unfold R.set_value in Hset;
    destruct (R.equivalent (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)));
    [inversion Hset; subst; exact Hbelow |].
  rewrite Hcontrolled in Hset; cbn in Hset.
  destruct (R.equivalent (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)));
    inversion Hset; subst; try exact Hbelow.
  unfold queue_below; cbn [R.with_queue R.queue R.with_readers R.ranking R.enqueue_all R.with_sigma R.readers R.rank_lt];
    apply insert_all_lower; [exact Hreaders |exact Hbelow].
Qed.

Lemma get_phase st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  R.frame_phase next_fr = R.frame_phase fr.
Proof. unfold R.complete_get; intro H; split_program H; reflexivity. Qed.
Lemma budget_get support st fr target next next_fr value owner phase :
  R.complete_get st fr target = (next,next_fr,value) ->
  budget_le (round_budget support next owner phase) (round_budget support st owner phase).
Proof.
  intro Hget; pose proof (get_layout Hget) as [_ [_ [Hcontrib [Hcells _]]]].
  apply budget_growth.
  - exact (proj1 (preserves_live_get Hget)).
  - eapply controlled_get; exact Hget.
  - rewrite (@incident_credit_layout support st next owner Hcells Hcontrib); lia.
  - intro Hcontrolled; rewrite (get_sigma_value owner Hget); lia.
Qed.
Lemma budget_materialize support st target owner phase :
  budget_le (round_budget support (R.materialize st target) owner phase) (round_budget support st owner phase).
Proof.
  apply budget_growth.
  - apply preserves_live_materialize.
  - apply controlled_layout; unfold R.materialize; destruct (M.lookup (R.sigma st) target); reflexivity.
  - rewrite (@incident_credit_layout support st (R.materialize st target) owner
      ltac:(unfold R.materialize; destruct (M.lookup (R.sigma st) target); reflexivity)
      ltac:(unfold R.materialize; destruct (M.lookup (R.sigma st) target); reflexivity)); lia.
  - intro Hcontrolled; rewrite materialize_sigma_value; lia.
Qed.
Lemma budget_materialize_new support st target owner phase : In target support -> R.is_materialized st target = false ->
  budget_lt (round_budget support (R.materialize st target) owner phase) (round_budget support st owner phase).
Proof.
  intros Hin Hmissing; unfold round_budget; apply Relation_Operators.left_slex.
  eapply missing_count_strict; [apply preserves_live_materialize |exact Hin |exact Hmissing |apply materialize_live].
Qed.
Lemma budget_observe support st target owner phase : round_budget support (R.observe st target) owner phase = round_budget support st owner phase.
Proof. unfold R.observe; destruct (Ranks.observe (R.ranking st) target); reflexivity. Qed.
Lemma budget_queue support st queue owner phase : round_budget support (R.with_queue st queue) owner phase = round_budget support st owner phase.
Proof. reflexivity. Qed.
Lemma budget_promote_new support st owner phase : S.mem owner (R.controlled st) = false ->
  budget_lt (round_budget support (R.promote_controlled st owner) owner phase) (round_budget support st owner phase).
Proof.
  intro Hmissing; unfold round_budget, promotion_reserve.
  assert (Hmem : S.mem owner (S.add owner (R.controlled st)) = true) by (apply SL.add_spec; auto).
  cbn [R.promote_controlled R.with_controlled R.controlled]; rewrite Hmissing, Hmem.
  apply Relation_Operators.right_slex, Relation_Operators.left_slex; lia.
Qed.

(** Parent phases stay in the suspended frames while a higher episode runs. *)
Fixpoint stack_phase k owner : option U.phase :=
  match k with
  | R.KLoop | R.KSeedLoop _ => None
  | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest
  | R.KDead fr _ _ rest | R.KDrain fr rest =>
      if V.eq_dec owner (R.frame_owner fr) then Some (R.frame_phase fr) else stack_phase rest owner
  end.
Definition owner_phase ctrl owner :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => None
  | R.StartEpisode _ k | R.Return k => stack_phase k owner
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k =>
      if V.eq_dec owner (R.frame_owner fr) then Some (R.frame_phase fr) else stack_phase k owner
  end.
Lemma stack_phase_present k owner phase : stack_phase k owner = Some phase -> In owner (suspended_owners k).
Proof.
  induction k; cbn; intro H; try discriminate.
  all: destruct (V.eq_dec owner (R.frame_owner f)) as [-> |Hneq]; [left; reflexivity |right; apply IHk; exact H].
Qed.
Lemma owner_phase_present ctrl owner phase : owner_phase ctrl owner = Some phase -> In owner (active_owners ctrl).
Proof.
  destruct ctrl; cbn [owner_phase active_owners]; intro H; try discriminate;
    try solve [eapply stack_phase_present; exact H];
    try solve [right; eapply stack_phase_present; exact H].
  all: destruct (V.eq_dec owner (R.frame_owner f)) as [-> |Hneq]; [left; reflexivity |right; eapply stack_phase_present; exact H].
Qed.
Definition larger_active st ctrl owner := exists child,
  In child (active_owners ctrl) /\ R.rank_lt st owner child = true.
Lemma larger_below_head st head rest owner : ordered (R.ranking st) (head :: rest) ->
  (exists child, In child (head :: rest) /\ R.rank_lt st owner child = true) -> R.rank_lt st owner head = true.
Proof.
  intros Horder [child [[<- |Hin] Hhigher]]; [exact Hhigher |].
  destruct (ordered_tail Horder) as [_ Hbelow]; rewrite Forall_forall in Hbelow.
  eapply lt_trans; [exact Hhigher |apply Hbelow; exact Hin].
Qed.
Lemma higher_not_equal st owner child : R.rank_lt st owner child = true -> owner <> child.
Proof. intros Hlt ->; unfold R.rank_lt in Hlt; rewrite lt_irrefl in Hlt; discriminate. Qed.
Lemma next_lower_phase tf roots before after owner phase : reachable tf roots before ->
  larger_active (R.cfg_state before) (R.cfg_control before) owner ->
  owner_phase (R.cfg_control before) owner = Some phase -> step tf before after ->
  owner_phase (R.cfg_control after) owner = Some phase.
Proof.
  intros Hreachable Hlarger Hphase Hstep.
  pose proof (@reachable_active_ordered tf roots before Hreachable) as Hordered.
  destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    unfold active_ordered in Hordered;
    cbn [R.cfg_state R.cfg_control] in Hstep, Hlarger, Hphase, Hordered.
  destruct ctrl as [|rs|rs|child k|fr body k|fr direct pending k|fr direct k|fr k|k];
    cbn [R.cfg_control owner_phase active_owners] in Hstep, Hphase, Hordered;
    try discriminate.
  all: try match type of Hordered with ordered _ (?head :: ?rest) =>
    assert (Hhigher : R.rank_lt st owner head = true) by (eapply larger_below_head; [exact Hordered |exact Hlarger]);
    assert (Hneq : owner <> head) by (eapply higher_not_equal; exact Hhigher)
  end.
  all: try (destruct (V.eq_dec owner (R.frame_owner fr)); [contradiction |]).
  all: try solve [inversion Hstep; subst; exact Hphase].
  all: unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep.
  all: repeat match goal with
  | Hget : R.complete_get _ _ _ = (_,_,_) |- _ =>
      let Ho := fresh "get_owner" in let Hp := fresh "get_phase" in
      pose proof (get_owner Hget) as Ho; pose proof (get_phase Hget) as Hp; clear Hget
  | Hset : R.set_value ?st ?fr ?direct = (?next,?next_fr) |- _ =>
      let Hv := fresh "commit_view" in pose proof (@commit_footprint st fr direct next next_fr Hset) as Hv;
      let Ho := fresh "commit_owner" in pose proof (commit_owner Hv) as Ho; clear Hset Hv
  end.
  all: cbn [R.cfg_control owner_phase stack_phase R.frame_owner R.frame_phase R.with_frame_side R.fresh_frame] in *;
    repeat match goal with Ho : R.frame_owner _ = _ |- _ => rewrite Ho in *; clear Ho end;
    try exact Hphase;
    try solve [destruct (V.eq_dec owner (R.frame_owner fr)); [contradiction |exact Hphase]].
  all: try solve [destruct (V.eq_dec owner child); [contradiction |exact Hphase]].
  all: repeat match goal with Hp : R.frame_phase _ = R.frame_phase _ |- _ => rewrite Hp; clear Hp end; exact Hphase.
Qed.

Lemma budget_lt_cases a b c x y z : budget_lt (a,(b,c)) (x,(y,z)) <->
  a < x \/ a = x /\ (b < y \/ b = y /\ c < z).
Proof.
  unfold budget_lt; split.
  - intro H; inversion H; subst; [left; assumption |right; split; [reflexivity |]].
    inversion H1; subst; auto.
  - intros [Hfirst |[-> [Hsecond |[-> Hlast]]]].
    + apply Relation_Operators.left_slex; exact Hfirst.
    + apply Relation_Operators.right_slex, Relation_Operators.left_slex; exact Hsecond.
    + repeat apply Relation_Operators.right_slex; exact Hlast.
Qed.
Lemma budget_lt_trans left middle right : budget_lt left middle -> budget_lt middle right -> budget_lt left right.
Proof.
  destruct left as [a [b c]], middle as [x [y z]], right as [u [v w]];
    rewrite !budget_lt_cases; intros H1 H2; destruct H1 as [H1 |[H1 [H1' |[H1' H1'']]]];
    destruct H2 as [H2 |[H2 [H2' |[H2' H2'']]]]; subst; intuition lia.
Qed.
Lemma budget_le_trans a b c : budget_le a b -> budget_le b c -> budget_le a c.
Proof. unfold budget_le; intros [-> |Hab] [-> |Hbc]; auto; right; eapply budget_lt_trans; eauto. Qed.
Lemma budget_lt_le a b c : budget_lt a b -> budget_le b c -> budget_lt a c.
Proof. intros Hab [-> |Hbc]; auto; eapply budget_lt_trans; eauto. Qed.
Lemma budget_le_lt a b c : budget_le a b -> budget_lt b c -> budget_lt a c.
Proof. intros [-> |Hab] Hbc; auto; eapply budget_lt_trans; eauto. Qed.
Lemma budget_layout support before after owner phase : R.sigma after = R.sigma before ->
  R.controlled after = R.controlled before -> R.side_cells after = R.side_cells before ->
  R.contributions after = R.contributions before ->
  round_budget support after owner phase = round_budget support before owner phase.
Proof.
  intros Hs Hc Hcells Hcontrib; unfold round_budget, missing_count, promotion_reserve, owner_credit,
    incident_credit, side_credit, R.is_materialized, R.sigma_value, R.stored_side_cell, R.stored_contribution;
    now rewrite Hs, Hc, Hcells, Hcontrib.
Qed.
Lemma budget_commit_other support st fr direct next next_fr owner phase :
  R.set_value st fr direct = (next,next_fr) -> owner <> R.frame_owner fr ->
  budget_le (round_budget support next owner phase) (round_budget support st owner phase).
Proof.
  intros Hset Hother; pose proof (@commit_footprint st fr direct next next_fr Hset) as Hv.
  apply budget_growth.
  - eapply preserves_live_commit; exact Hset.
  - eapply controlled_commit; exact Hset.
  - rewrite (@incident_credit_layout support st next owner (commit_cells Hv) (commit_contributions Hv)); lia.
  - intro Hcontrolled; unfold R.sigma_value; rewrite (commit_other Hv Hother); lia.
Qed.
Lemma budget_requeue support before after written owner phase :
  round_budget support (R.requeue_changed_controlled_owner before after written) owner phase = round_budget support after owner phase.
Proof. reflexivity. Qed.
Lemma next_budget_below_active tf roots support before after owner phase : reachable tf roots before ->
  larger_active (R.cfg_state before) (R.cfg_control before) owner -> step tf before after ->
  budget_le (round_budget support (R.cfg_state after) owner phase) (round_budget support (R.cfg_state before) owner phase).
Proof.
  intros Hreachable Hlarger Hstep.
  pose proof (@reachable_active_ordered tf roots before Hreachable) as Hordered.
  pose proof (@reachable_scoped_config tf roots before Hreachable) as [Hscoped _].
  destruct before as [st ctrl]; unfold step, R.next_config in Hstep; unfold active_ordered in Hordered;
    cbn [R.cfg_state R.cfg_control] in Hstep, Hlarger, Hordered, Hscoped.
  destruct ctrl; cbn [R.cfg_control active_owners] in Hstep, Hordered.
  all: try solve [unfold larger_active in Hlarger; cbn [active_owners] in Hlarger;
    destruct Hlarger as [child [Hin _]]; contradiction].
  all: try match type of Hordered with ordered _ (?head :: ?rest) =>
    assert (Hhigher : R.rank_lt st owner head = true) by (eapply larger_below_head; [exact Hordered |exact Hlarger]);
    assert (Hneq : owner <> head) by (eapply higher_not_equal; exact Hhigher)
  end.
  all: unfold R.continue_side, R.continue_dead in Hstep; split_program Hstep.
  all: cbn [R.cfg_state] in *; repeat rewrite budget_requeue; unfold R.enqueue; repeat rewrite budget_queue.
  all: try solve [left; eapply budget_layout; reflexivity].
  all: try solve [left; apply budget_observe].
  all: try solve [apply budget_materialize].
  all: try solve [left; apply budget_higher_close; assumption].
  all: try solve [eapply budget_le_trans; [apply budget_materialize |left; apply budget_observe]].
  all: try solve [match goal with Hget : R.complete_get ?base _ _ = (?next,_,_) |- _ =>
    eapply budget_le_trans with (b := round_budget support base owner phase);
      [eapply budget_get; exact Hget |];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    left; try reflexivity; apply budget_observe end].
  all: try solve [match goal with Hwrite : R.write_side_contribution ?base _ _ _ = (?next,_) |- _ =>
    eapply budget_le_trans with (b := round_budget support base owner phase);
      [eapply budget_write; exact Hwrite |left; try reflexivity; apply budget_observe] end].
  all: try solve [match goal with Hset : R.set_value _ _ _ = (_,_) |- _ =>
    eapply budget_commit_other; [exact Hset |exact Hneq] end].
  all: try solve [rewrite budget_higher_close by assumption; left; reflexivity].
Qed.


(** A finite episode trace stops before its caller can resume. This also
    prevents the next episode's initial phase from entering a round budget. *)
Inductive episode_steps tf owner : R.config -> R.config -> Prop :=
| episode_refl c : episode_steps tf owner c c
| episode_cons before next after :
    In owner (active_owners (R.cfg_control before)) ->
    step tf before next -> episode_steps tf owner next after -> episode_steps tf owner before after.
Lemma episode_path tf owner before after : episode_steps tf owner before after -> steps tf before after.
Proof. intro H; induction H; eauto using steps. Qed.
Lemma episode_append tf owner a b c : episode_steps tf owner a b -> episode_steps tf owner b c -> episode_steps tf owner a c.
Proof. intros Hab Hbc; induction Hab; eauto using episode_steps. Qed.

Fixpoint stack_episode owner base k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => False
  | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest
  | R.KDead fr _ _ rest | R.KDrain fr rest =>
      (R.frame_owner fr = owner /\ rest = base) \/ stack_episode owner base rest
  end.
Definition episode_scope owner base ctrl : Prop :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
  | R.StartEpisode child k => (child = owner /\ k = base) \/ stack_episode owner base k
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k =>
      (R.frame_owner fr = owner /\ k = base) \/ stack_episode owner base k
  | R.Return k => stack_episode owner base k
  end.
Fixpoint stack_depth k : nat :=
  match k with
  | R.KLoop | R.KSeedLoop _ => 0
  | R.KAfterGet _ _ _ rest | R.KAfterSide _ _ rest | R.KAfterSpawn _ _ rest
  | R.KDead _ _ _ rest | R.KDrain _ rest => S (stack_depth rest)
  end.
Lemma stack_episode_deeper owner base k : stack_episode owner base k -> stack_depth base < stack_depth k.
Proof.
  induction k; cbn; intros H; try contradiction.
  all: destruct H as [[_ ->] |H]; [lia |apply IHk in H; lia].
Qed.
Lemma episode_return_outside owner k : ~ episode_scope owner k (R.Return k).
Proof. cbn [episode_scope]; intro H; apply stack_episode_deeper in H; lia. Qed.
Lemma stack_episode_active owner base k : stack_episode owner base k -> In owner (suspended_owners k).
Proof.
  induction k; cbn; intro H; try contradiction.
  all: destruct H as [[<- _] |H]; [auto |right; apply IHk; exact H].
Qed.
Lemma episode_scope_active owner base ctrl : episode_scope owner base ctrl -> In owner (active_owners ctrl).
Proof.
  destruct ctrl; cbn [episode_scope active_owners]; intro H; try contradiction;
    try solve [apply stack_episode_active in H; exact H].
  all: destruct H as [[Howner _] |H]; [left; exact Howner |right; eapply stack_episode_active; exact H].
Qed.
Lemma next_episode_scope tf before after owner base : episode_scope owner base (R.cfg_control before) ->
  step tf before after -> episode_scope owner base (R.cfg_control after) \/
  exists fr, R.cfg_control before = R.RunDrain fr base /\ R.frame_owner fr = owner /\ R.cfg_control after = R.Return base.
Proof.
  intros Hscope Hstep; destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep, Hscope.
  destruct ctrl; cbn [R.cfg_control episode_scope] in Hstep, Hscope; try contradiction.
  all: unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep; split_program Hstep; primitive_views.
  all: cbn [R.cfg_control episode_scope stack_episode R.frame_owner R.fresh_frame R.with_frame_side] in *;
    repeat match goal with Ho : R.frame_owner _ = R.frame_owner _ |- _ => rewrite Ho in *; clear Ho end.
  all: try solve [left; intuition auto].
  all: destruct Hscope as [[Howner Hbase] |Hscope]; [subst; right; eexists; repeat split; reflexivity |left; exact Hscope].
Qed.


Lemma closing_queue_below tf roots before after owner : reachable tf roots before ->
  step tf before after -> closing before after owner -> queue_below (R.cfg_state after) owner.
Proof.
  intros Hreachable Hstep [fr [k [Hbefore [Hafter Howner]]]].
  pose proof (@reachable_rank_configuration tf roots before Hreachable) as [Hstore Hrefs].
  destruct before as [st ctrl]; cbn [R.cfg_control R.cfg_state] in *; subst ctrl owner.
  cbn [control_refs] in Hrefs; destruct Hrefs as [Hfr Hk].
  assert (Howner_ranked : ranked (R.ranking st) (R.frame_owner fr)) by (exact (proj2 (ref_owner Hfr))).
  unfold step, R.next_config in Hstep; cbn [R.cfg_control R.cfg_state] in Hstep.
  destruct (R.queue st) as [|head rest] eqn:Hqueue; cbn [R.queue_peek R.queue_pop] in Hstep.
  - inversion Hstep; subst; apply queue_below_close; unfold queue_below; rewrite Hqueue; constructor.
  - destruct (V.eq_dec head (R.frame_owner fr)) as [Heq |Hneq].
    + inversion Hstep; subst; discriminate.
    + destruct (R.rank_lt st (R.frame_owner fr) head) eqn:Hhigher.
      * inversion Hstep; subst; discriminate.
      * inversion Hstep; subst; apply queue_below_close.
        assert (Hhead : ranked (R.ranking st) head).
        { pose proof (known_ranked_queue Hstore) as Hq; rewrite Hqueue in Hq; inversion Hq; assumption. }
        assert (Hlower : R.rank_lt st head (R.frame_owner fr) = true).
        { destruct (@lt_compare (R.ranking st) head (R.frame_owner fr) (store_valid Hstore)
            Hhead Howner_ranked Hneq) as [Hlt |Hlt]; [exact Hlt |unfold R.rank_lt in Hhigher; congruence]. }
        unfold queue_below; rewrite Hqueue; constructor; [exact Hlower |].
        destruct (@ordered_tail (R.ranking st) head rest ltac:(rewrite <- Hqueue; exact (store_ordered Hstore))) as [_ Htail].
        rewrite Forall_forall in *; intros x Hin; eapply lt_trans; [apply Htail; exact Hin |exact Hlower].
Qed.
Lemma first_episode_return tf roots owner base before final : reachable tf roots before ->
  episode_scope owner base (R.cfg_control before) -> steps tf before (configuration final (R.Return base)) ->
  exists returned, episode_steps tf owner before (configuration returned (R.Return base)) /\ queue_below returned owner.
Proof.
  intros Hreachable Hscope Hpath.
  assert (Houtside : ~ episode_scope owner base (R.cfg_control (configuration final (R.Return base))))
    by (apply episode_return_outside).
  revert Hreachable Hscope Houtside; induction Hpath; intros Hreachable Hscope Houtside.
  - contradiction.
  - destruct (@next_episode_scope tf before next owner base Hscope H) as [Hnext |[fr [Hbefore [Howner Hreturn]]]].
    + destruct (IHHpath (reachable_advance Hreachable H) Hnext Houtside) as [returned [Htail Hbelow]].
      exists returned; split; [eapply episode_cons; [eapply episode_scope_active; exact Hscope |exact H |exact Htail] |exact Hbelow].
    + assert (Hclosing : closing before next owner) by (exists fr, base; repeat split; auto).
      pose proof (closing_queue_below Hreachable H Hclosing) as Hbelow.
      destruct next as [returned ctrl]; cbn [R.cfg_control R.cfg_state] in Hreturn, Hbelow; subst ctrl.
      exists returned; split; [eapply episode_cons; [eapply episode_scope_active; exact Hscope |exact H |constructor] |exact Hbelow].
Qed.
Definition episode_finished tf start owner k := exists final,
  episode_steps tf owner start (configuration final (R.Return k)) /\ queue_below final owner.
Theorem episode_first_return tf roots st owner k : reachable tf roots (configuration st (R.StartEpisode owner k)) ->
  episode_complete tf (configuration st (R.StartEpisode owner k)) owner k ->
  episode_finished tf (configuration st (R.StartEpisode owner k)) owner k.
Proof.
  intros Hreachable [final [Hpath _]]; eapply first_episode_return;
    [exact Hreachable |left; auto |exact Hpath].
Qed.
Theorem higher_episode_parent_budget tf roots support owner child before after phase :
  reachable tf roots before -> R.rank_lt (R.cfg_state before) owner child = true ->
  owner_phase (R.cfg_control before) owner = Some phase -> episode_steps tf child before after ->
  owner_phase (R.cfg_control after) owner = Some phase /\
  budget_le (round_budget support (R.cfg_state after) owner phase) (round_budget support (R.cfg_state before) owner phase).
Proof.
  intros Hreachable Hhigher Hphase Hpath; revert Hreachable Hhigher Hphase; induction Hpath;
    intros Hreachable Hhigher Hphase; [split; [exact Hphase |left; reflexivity] |].
  assert (Hlarger : larger_active (R.cfg_state before) (R.cfg_control before) owner) by (exists child; auto).
  assert (Hnext_phase : owner_phase (R.cfg_control next) owner = Some phase) by (eapply next_lower_phase; eauto).
  assert (Hnext_higher : R.rank_lt (R.cfg_state next) owner child = true).
  { eapply lt_extends; [eapply next_ranking_extends; exact H0 |exact Hhigher]. }
  destruct (IHHpath (reachable_advance Hreachable H0) Hnext_higher Hnext_phase) as [Hfinal Hbudget].
  split; [exact Hfinal |eapply budget_le_trans; [exact Hbudget |eapply next_budget_below_active; eauto]].
Qed.


Lemma ordered_member_lower st head rest owner : ordered (R.ranking st) (head :: rest) ->
  In owner (head :: rest) -> owner <> head -> R.rank_lt st owner head = true.
Proof.
  intros Hordered [Heq |Hin] Hneq; [congruence |].
  destruct (ordered_tail Hordered) as [_ Hbelow]; rewrite Forall_forall in Hbelow; apply Hbelow; exact Hin.
Qed.
Theorem next_owner_budget tf roots support before after owner phase next_phase : reachable tf roots before ->
  owner_phase (R.cfg_control before) owner = Some phase ->
  owner_phase (R.cfg_control after) owner = Some next_phase -> step tf before after ->
  budget_le (round_budget support (R.cfg_state after) owner next_phase)
    (round_budget support (R.cfg_state before) owner phase).
Proof.
  intros Hreachable Hphase Hnext_phase Hstep; pose proof Hphase as Htracked.
  pose proof (@reachable_active_ordered tf roots before Hreachable) as Hordered.
  pose proof (@reachable_owners_unique tf roots before Hreachable) as Hunique.
  pose proof (@owner_phase_present (R.cfg_control before) owner phase Hphase) as Hin.
  destruct before as [st ctrl]; cbn [R.cfg_control R.cfg_state] in *; unfold active_ordered in Hordered.
  destruct ctrl; cbn [R.cfg_control R.cfg_state active_owners owner_phase] in Hordered, Hunique, Hin, Hphase; try discriminate.
  all: try match goal with k : R.continuation, Hord : ordered _ (suspended_owners ?k) |- _ =>
    destruct k; cbn [suspended_owners stack_phase] in Hordered, Hunique, Hin, Hphase; try discriminate end.
  all: match type of Hordered with ordered _ (?head :: ?rest) =>
    destruct (V.eq_dec owner head) as [Heq |Hneq]; [subst owner |]
  end.
  all: try solve [match goal with Hneq : ?owner <> ?head, Hreach : reachable ?tf ?roots ?before |- _ =>
    assert (Hlarger : larger_active (R.cfg_state before) (R.cfg_control before) owner)
      by (exists head; split; [cbn [R.cfg_control active_owners]; left; reflexivity |cbn [R.cfg_state]; eapply ordered_member_lower; eauto]);
    pose proof (@next_lower_phase tf roots before after owner phase Hreach Hlarger Htracked Hstep) as Hkeep;
    rewrite Hkeep in Hnext_phase; inversion Hnext_phase; subst next_phase;
    exact (@next_budget_below_active tf roots support before after owner phase Hreach Hlarger Hstep) end].
  all: try solve [inversion Hunique; subst; exfalso; apply H1; eapply stack_phase_present; exact Hphase].
  all: unfold step, R.next_config in Hstep; cbn [R.cfg_control R.cfg_state] in Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep; split_program Hstep.
  all: repeat match goal with
  | Hget : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- budget_le (round_budget ?support _ ?owner _) (round_budget _ _ _ ?phase) =>
      let Ho := fresh "get_owner" in let Hp := fresh "get_phase" in
      pose proof (get_owner Hget) as Ho; pose proof (get_phase Hget) as Hp;
      let Hg := fresh "get_budget" in pose proof (@budget_get support base fr target next next_fr value owner phase Hget) as Hg; clear Hget
  | Hset : R.set_value ?base ?fr ?direct = (?next,?next_fr) |- _ =>
      let Hv := fresh "commit_view" in let Ho := fresh "commit_owner" in
      pose proof (@commit_footprint base fr direct next next_fr Hset) as Hv;
      pose proof (commit_owner Hv) as Ho;
      let Hb := fresh "commit_budget" in pose proof (@budget_commit support base fr direct next next_fr Hset) as Hb; clear Hv Hset
  end.
  all: cbn [R.cfg_control owner_phase stack_phase R.frame_owner R.frame_phase R.with_frame_side R.fresh_frame] in Hnext_phase;
    repeat match goal with Ho : R.frame_owner _ = _ |- _ => rewrite Ho in Hnext_phase; clear Ho end.
  all: repeat match goal with H : context [if V.eq_dec ?x ?x then _ else _] |- _ =>
      destruct (V.eq_dec x x); [|contradiction] end.
  all: repeat match goal with Hp : R.frame_phase _ = R.frame_phase _ |- _ => rewrite Hp in Hnext_phase; clear Hp end.
  all: try (injection Hphase as Hphase; subst phase);
    try (injection Hnext_phase as Hnext_phase; subst next_phase).
  all: cbn [R.cfg_state]; repeat rewrite budget_requeue; unfold R.enqueue; repeat rewrite budget_queue.
  all: try assumption.
  all: try solve [left; reflexivity].
  all: try solve [left; apply budget_observe].
  all: try solve [eapply budget_commit; eauto].
  all: try solve [eapply budget_write; eauto].
  all: try solve [eapply budget_le_trans; [apply budget_materialize |left; apply budget_observe]].
  all: try solve [match goal with Hg : budget_le _ (round_budget ?xs ?base _ _) |- _ =>
    eapply budget_le_trans; [exact Hg |]; repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      left; try reflexivity; apply budget_observe end].
  all: try solve [match goal with Hwrite : R.write_side_contribution ?base _ _ _ = (_,_) |- _ =>
    eapply budget_le_trans; [eapply budget_write; exact Hwrite |left; apply budget_observe] end].
  all: inversion Hunique as [|head rest Hnot Hdup]; subst; exfalso; apply Hnot;
    eapply stack_phase_present; exact Hnext_phase.
Qed.


Lemma stack_phase_exists k owner : In owner (suspended_owners k) -> exists phase, stack_phase k owner = Some phase.
Proof.
  induction k; cbn; intro Hin; try contradiction.
  all: destruct (V.eq_dec owner (R.frame_owner f)) as [Heq |Hneq]; [eexists; reflexivity |].
  all: destruct Hin as [Heq |Hin]; [congruence |apply IHk; exact Hin].
Qed.
Lemma owner_phase_exists ctrl owner : In owner (framed_owners ctrl) -> exists phase, owner_phase ctrl owner = Some phase.
Proof.
  destruct ctrl; cbn [framed_owners active_owners owner_phase]; intro Hin; try contradiction;
    try solve [apply stack_phase_exists; exact Hin].
  all: destruct (V.eq_dec owner (R.frame_owner f)) as [Heq |Hneq]; [eexists; reflexivity |].
  all: destruct Hin as [Heq |Hin]; [congruence |apply stack_phase_exists; exact Hin].
Qed.
Lemma owner_phase_framed ctrl owner phase : owner_phase ctrl owner = Some phase -> In owner (framed_owners ctrl).
Proof.
  destruct ctrl; cbn [framed_owners active_owners owner_phase]; intro Hphase; try discriminate;
    try solve [eapply stack_phase_present; exact Hphase].
  all: destruct (V.eq_dec owner (R.frame_owner f)) as [-> |Hneq]; [left; reflexivity |right; eapply stack_phase_present; exact Hphase].
Qed.
Lemma next_framed_origin tf before after : step tf before after -> forall owner,
  In owner (framed_owners (R.cfg_control before)) ->
  In owner (framed_owners (R.cfg_control after)) \/ closing before after owner.
Proof.
  intro Hstep; destruct before as [st ctrl]; unfold step, R.next_config in Hstep;
    cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [R.cfg_control] in Hstep;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep;
    split_program Hstep; primitive_views.
  all: cbn [R.cfg_state R.cfg_control framed_owners active_owners suspended_owners R.frame_owner R.fresh_frame R.with_frame_side] in *;
    repeat match goal with Ho : R.frame_owner _ = R.frame_owner _ |- _ => rewrite Ho in *; clear Ho end;
    intros owner Hin; try solve [left; cbn; intuition auto].
  all: destruct Hin as [<- |Hin]; [right; eexists; eexists; repeat split; reflexivity |left; exact Hin].
Qed.
Lemma closing_owner_inactive before after owner : NoDup (active_owners (R.cfg_control before)) ->
  closing before after owner -> ~ In owner (active_owners (R.cfg_control after)).
Proof.
  intros Hunique [fr [k [Hbefore [Hafter ->]]]]; rewrite Hbefore in Hunique; rewrite Hafter;
    cbn [active_owners] in *; inversion Hunique; assumption.
Qed.
Lemma next_owner_phase_exists tf roots before after owner phase : reachable tf roots before ->
  owner_phase (R.cfg_control before) owner = Some phase -> step tf before after ->
  In owner (active_owners (R.cfg_control after)) -> exists next_phase, owner_phase (R.cfg_control after) owner = Some next_phase.
Proof.
  intros Hreachable Hphase Hstep Hactive.
  destruct (@next_framed_origin tf before after Hstep owner
    (@owner_phase_framed (R.cfg_control before) owner phase Hphase)) as [Hframed |Hclosing].
  - apply owner_phase_exists; exact Hframed.
  - exfalso; eapply closing_owner_inactive; [eapply reachable_owners_unique; exact Hreachable |exact Hclosing |exact Hactive].
Qed.
Lemma episode_continues_or_done tf owner before after : episode_steps tf owner before after ->
  before = after \/ In owner (active_owners (R.cfg_control before)).
Proof. intro H; destruct H; auto. Qed.
Theorem episode_owner_budget tf roots support owner before after phase next_phase : reachable tf roots before ->
  owner_phase (R.cfg_control before) owner = Some phase -> owner_phase (R.cfg_control after) owner = Some next_phase ->
  episode_steps tf owner before after ->
  budget_le (round_budget support (R.cfg_state after) owner next_phase)
    (round_budget support (R.cfg_state before) owner phase).
Proof.
  intros Hreachable Hphase Hfinal Hpath; revert phase Hreachable Hphase; induction Hpath; intros phase Hreachable Hphase.
  - rewrite Hphase in Hfinal; injection Hfinal as ->; left; reflexivity.
  - assert (Hnext_reachable := reachable_advance Hreachable H0).
    assert (Hnext_phase : exists p, owner_phase (R.cfg_control next) owner = Some p).
    { destruct (episode_continues_or_done Hpath) as [-> |Hactive]; [exists next_phase; exact Hfinal |].
      exact (@next_owner_phase_exists tf roots before next owner phase Hreachable Hphase H0 Hactive). }
    destruct Hnext_phase as [p Hp].
    eapply budget_le_trans; [exact (IHHpath Hfinal p Hnext_reachable Hp) |].
    exact (@next_owner_budget tf roots support before next owner phase p Hreachable Hphase Hp H0).
Qed.
Lemma budget_lt_irrefl b : ~ budget_lt b b.
Proof. destruct b as [a [b c]]; rewrite budget_lt_cases; lia. Qed.
Lemma budget_le_antisym a b : budget_le a b -> budget_le b a -> a = b.
Proof.
  intros [-> |Hab] [Heq |Hba]; auto; exfalso; apply (@budget_lt_irrefl a); eapply budget_lt_trans; eauto.
Qed.
Lemma episode_budget_strict tf roots support owner before middle next after phase middle_phase next_phase final_phase :
  reachable tf roots before -> episode_steps tf owner before middle -> step tf middle next -> episode_steps tf owner next after ->
  owner_phase (R.cfg_control before) owner = Some phase -> owner_phase (R.cfg_control middle) owner = Some middle_phase ->
  owner_phase (R.cfg_control next) owner = Some next_phase -> owner_phase (R.cfg_control after) owner = Some final_phase ->
  budget_lt (round_budget support (R.cfg_state next) owner next_phase)
    (round_budget support (R.cfg_state middle) owner middle_phase) ->
  budget_lt (round_budget support (R.cfg_state after) owner final_phase) (round_budget support (R.cfg_state before) owner phase).
Proof.
  intros Hreachable Hprefix Hstep Hsuffix Hphase Hmiddle Hnext Hfinal Hstrict.
  assert (Hmiddle_reachable := reachable_follow Hreachable (episode_path Hprefix)).
  eapply budget_lt_le; [|exact (@episode_owner_budget tf roots support owner before middle phase middle_phase Hreachable Hphase Hmiddle Hprefix)].
  eapply budget_le_lt; [|exact Hstrict].
  exact (@episode_owner_budget tf roots support owner next after next_phase final_phase
    (reachable_advance Hmiddle_reachable Hstep) Hnext Hfinal Hsuffix).
Qed.


Lemma equal_budget_no_discovery support before after owner phase next_phase target :
  round_budget support after owner next_phase = round_budget support before owner phase ->
  preserves_live before after -> In target support -> solved after target -> R.is_materialized before target = true.
Proof.
  intros Hbudget Hlive Hin Hsolved; destruct (R.is_materialized before target) eqn:Hmat; [reflexivity |].
  pose proof (@missing_count_strict support before after target Hlive Hin Hmat Hsolved) as Hstrict.
  apply (f_equal (@fst nat (nat * nat))) in Hbudget; unfold round_budget in Hbudget; cbn in Hbudget; lia.
Qed.
Lemma queue_below_layout before after owner : R.queue after = R.queue before ->
  extends (R.ranking before) (R.ranking after) -> queue_below before owner -> queue_below after owner.
Proof.
  intros Hq He Hbelow; unfold queue_below in *; rewrite Hq;
    eapply Forall_impl; [intros x Hx; exact (@lt_extends (R.ranking before) (R.ranking after) x owner He Hx) |exact Hbelow].
Qed.
Lemma queue_below_observe st target owner : queue_below st owner -> queue_below (R.observe st target) owner.
Proof. intro H; eapply queue_below_layout with (before := st); [unfold R.observe; destruct (Ranks.observe (R.ranking st) target); reflexivity |apply observe_extends |exact H]. Qed.
Lemma observe_materialized st observed target : R.is_materialized (R.observe st observed) target = R.is_materialized st target.
Proof. unfold R.observe; destruct (Ranks.observe (R.ranking st) observed); reflexivity. Qed.
Lemma commit_equivalent_queue st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  R.equivalent (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) = true -> R.queue next = R.queue st.
Proof.
  unfold R.set_value; intro Hset; split_program Hset; intro Hsame; try reflexivity.
  all: unfold R.sigma_value in Hsame; cbn [R.with_sigma R.with_queue R.with_readers R.enqueue_all R.sigma] in Hsame;
    rewrite ML.lookup_update_same in Hsame; cbn in Hsame;
    fold (R.sigma_value st (R.frame_owner fr)) in Hsame; cbn in Heqb0; congruence.
Qed.
Lemma drain_lower_returns tf st fr k after : queue_below st (R.frame_owner fr) ->
  step tf (configuration st (R.RunDrain fr k)) after -> R.cfg_control after = R.Return k.
Proof.
  intros Hbelow Hstep; unfold step, R.next_config in Hstep; cbn [configuration R.cfg_state R.cfg_control] in Hstep.
  destruct (R.queue st) as [|head rest] eqn:Hq; cbn [R.queue_peek R.queue_pop] in Hstep.
  - inversion Hstep; reflexivity.
  - unfold queue_below in Hbelow; rewrite Hq in Hbelow; inversion Hbelow as [|? ? Hlower Htail]; subst.
    destruct (V.eq_dec head (R.frame_owner fr)) as [Heq |Hneq]; [subst head; unfold R.rank_lt in Hlower; rewrite lt_irrefl in Hlower; discriminate |].
    assert (Hhigher : R.rank_lt st (R.frame_owner fr) head = false).
    { destruct (R.rank_lt st (R.frame_owner fr) head) eqn:Hlt; [|reflexivity].
      pose proof (@lt_trans (R.ranking st) head (R.frame_owner fr) head Hlower Hlt) as Hcycle;
        rewrite lt_irrefl in Hcycle; discriminate. }
    rewrite Hhigher in Hstep; inversion Hstep; reflexivity.
Qed.
Definition quiet_round support owner c := queue_below (R.cfg_state c) owner /\
  match R.cfg_control c with
  | R.RunRhs fr _ _ | R.RunDead fr _ _ _ | R.RunCommit fr _ _ | R.RunDrain fr _ => R.frame_owner fr = owner
  | R.StartEpisode child _ => In child support /\ R.is_materialized (R.cfg_state c) child = false
  | _ => False
  end.


Lemma phase_rhs fr body k : owner_phase (R.RunRhs fr body k) (R.frame_owner fr) = Some (R.frame_phase fr).
Proof. cbn [owner_phase]; destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr)); congruence. Qed.
Lemma phase_dead fr direct pending k : owner_phase (R.RunDead fr direct pending k) (R.frame_owner fr) = Some (R.frame_phase fr).
Proof. cbn [owner_phase]; destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr)); congruence. Qed.
Lemma phase_commit fr direct k : owner_phase (R.RunCommit fr direct k) (R.frame_owner fr) = Some (R.frame_phase fr).
Proof. cbn [owner_phase]; destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr)); congruence. Qed.
Lemma phase_drain fr k : owner_phase (R.RunDrain fr k) (R.frame_owner fr) = Some (R.frame_phase fr).
Proof. cbn [owner_phase]; destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr)); congruence. Qed.
Lemma phase_continue_side st fr target body k changed :
  owner_phase (R.cfg_control (R.continue_side st fr target body k changed)) (R.frame_owner fr) = Some (R.frame_phase fr).
Proof.
  unfold R.continue_side; destruct changed; [destruct (_ && _)%bool |];
    cbn [R.cfg_control owner_phase stack_phase]; destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr)); congruence.
Qed.
Lemma phase_continue_dead st fr direct target pending k changed :
  owner_phase (R.cfg_control (R.continue_dead st fr direct target pending k changed)) (R.frame_owner fr) = Some (R.frame_phase fr).
Proof.
  unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |];
    cbn [R.cfg_control owner_phase stack_phase]; destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr)); congruence.
Qed.
Lemma equal_commit_keeps_lower support st fr direct next next_fr :
  forward_readers st -> queue_below st (R.frame_owner fr) -> R.set_value st fr direct = (next,next_fr) ->
  round_budget support next (R.frame_owner fr) (R.frame_phase next_fr) = round_budget support st (R.frame_owner fr) (R.frame_phase fr) ->
  queue_below (R.requeue_changed_controlled_owner st next (R.frame_owner fr)) (R.frame_owner fr).
Proof.
  intros Hforward Hbelow Hset Hbudget; destruct (S.mem (R.frame_owner fr) (R.controlled st)) eqn:Hcontrolled.
  - assert (Hsame : R.equivalent (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) = true).
    { destruct (R.equivalent (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr))) eqn:Heq; [reflexivity |].
      pose proof (@budget_commit_changed support st fr direct next next_fr Hcontrolled Hset Heq) as Hstrict;
        rewrite Hbudget in Hstrict; exfalso; eapply budget_lt_irrefl; exact Hstrict. }
    unfold R.requeue_changed_controlled_owner; rewrite Hsame, andb_false_r; cbn.
    eapply queue_below_layout with (before := st);
      [cbn [R.with_queue R.queue]; exact (@commit_equivalent_queue st fr direct next next_fr Hset Hsame) | |exact Hbelow].
    cbn [R.with_queue R.ranking]; rewrite (commit_ranking (@commit_footprint st fr direct next next_fr Hset)); apply extends_refl.
  - eapply uncontrolled_commit_keeps_lower_queue; eauto.
Qed.


Lemma budget_enqueue support st target owner phase : round_budget support (R.enqueue st target) owner phase = round_budget support st owner phase.
Proof. reflexivity. Qed.
Lemma budget_continue_side support st fr target body k changed owner phase :
  round_budget support (R.cfg_state (R.continue_side st fr target body k changed)) owner phase = round_budget support st owner phase.
Proof. unfold R.continue_side; destruct changed; [destruct (_ && _)%bool |]; reflexivity. Qed.
Lemma budget_continue_dead support st fr direct target pending k changed owner phase :
  round_budget support (R.cfg_state (R.continue_dead st fr direct target pending k changed)) owner phase = round_budget support st owner phase.
Proof. unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; reflexivity. Qed.
Lemma equal_write_unchanged support st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) -> In (R.frame_owner fr) support -> In target support ->
  round_budget support next (R.frame_owner fr) (R.frame_phase fr) = round_budget support st (R.frame_owner fr) (R.frame_phase fr) -> changed = false.
Proof.
  intros Hwrite Howner Htarget Hbudget; destruct changed; [|reflexivity].
  pose proof (@budget_write_changed support st fr target input next (R.frame_owner fr) (R.frame_phase fr)
    Hwrite Howner Htarget (or_introl eq_refl)) as Hstrict.
  rewrite Hbudget in Hstrict; exfalso; eapply budget_lt_irrefl; exact Hstrict.
Qed.
Lemma queue_below_write st fr target input next changed owner : queue_below st owner ->
  R.write_side_contribution st fr target input = (next,changed) -> queue_below next owner.
Proof.
  intros Hbelow Hwrite; eapply queue_below_layout with (before := st);
    [exact (write_queue Hwrite) |rewrite (write_rank Hwrite); apply extends_refl |exact Hbelow].
Qed.
Lemma queue_below_get st fr target next next_fr value owner : queue_below st owner ->
  R.complete_get st fr target = (next,next_fr,value) -> queue_below next owner.
Proof.
  intros Hbelow Hget; eapply queue_below_layout with (before := st);
    [exact (get_queue Hget) |rewrite (get_rank Hget); apply extends_refl |exact Hbelow].
Qed.


Theorem next_quiet_round tf roots (finite : Sem.finite_system tf roots) before after owner phase next_phase :
  reachable tf roots before -> quiet_round (Sem.support finite) owner before ->
  owner_phase (R.cfg_control before) owner = Some phase -> owner_phase (R.cfg_control after) owner = Some next_phase ->
  round_budget (Sem.support finite) (R.cfg_state after) owner next_phase = round_budget (Sem.support finite) (R.cfg_state before) owner phase ->
  step tf before after -> quiet_round (Sem.support finite) owner after.
Proof.
  intros Hreachable [Hbelow Hquiet] Hphase Hnext_phase Hbudget Hstep.
  pose proof (@reachable_configuration_wf tf roots finite before Hreachable) as [Hstore Hrefs].
  pose proof (next_preserves_live Hstep) as Hlive.
  destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in *.
  destruct ctrl as [|rs|rs|child k|fr body k|fr direct pending k|fr direct k|fr k|k];
    cbn in Hquiet; try contradiction.
  - destruct Hquiet as [Hchild Hmissing]; unfold step, R.next_config in Hstep; cbn in Hstep; inversion Hstep; subst after.
    exfalso; pose proof (@equal_budget_no_discovery (Sem.support finite) st (R.materialize st child) owner phase next_phase child
      Hbudget Hlive Hchild (materialize_live st child)) as Hmat; congruence.
  - subst owner; cbn [control_refs] in Hrefs; destruct Hrefs as [Hfr [Hcode Hk]].
    rewrite phase_rhs in Hphase; injection Hphase as <-.
    pose proof (proj1 (ref_owner Hfr)) as Howner.
    pose proof (code_child_supported Hcode) as Hchild.
    destruct body as [direct|target tail|target input tail|target tail]; cbn in Hchild.
    + unfold step, R.next_config in Hstep; cbn [configuration R.cfg_state R.cfg_control] in Hstep; inversion Hstep; subst after.
      split; [exact Hbelow |reflexivity].
    + destruct Hchild as [Htarget Htail].
      set (observed := R.observe st target).
      destruct (negb (R.is_materialized observed target) && R.rank_lt observed (R.frame_owner fr) target) eqn:Hcall.
      * unfold step, R.next_config in Hstep; cbn -[R.observe R.complete_get] in Hstep; fold observed in Hstep; rewrite Hcall in Hstep;
          inversion Hstep; subst after.
        split; [apply queue_below_observe; exact Hbelow |].
        apply andb_true_iff in Hcall; destruct Hcall as [Hmissing _]; apply negb_true_iff in Hmissing; cbn [R.cfg_control R.cfg_state]; auto.
      * set (base := if R.is_materialized observed target then observed else R.enqueue observed target).
        destruct (R.complete_get base fr target) as [[next next_fr] value] eqn:Hget.
        unfold step, R.next_config in Hstep; cbn -[R.observe R.complete_get] in Hstep; fold observed in Hstep; rewrite Hcall in Hstep;
          fold base in Hstep; rewrite Hget in Hstep; inversion Hstep; subst after.
        assert (Hmaterialized : R.is_materialized st target = true).
        { eapply equal_budget_no_discovery; [exact Hbudget |exact Hlive |exact Htarget |exact (proj2 (preserves_live_get Hget))]. }
        assert (Hbase : base = observed) by (unfold base, observed; rewrite observe_materialized, Hmaterialized; reflexivity).
        change (queue_below next (R.frame_owner fr) /\ R.frame_owner next_fr = R.frame_owner fr); split;
          [eapply queue_below_get with (st := base); [rewrite Hbase; apply queue_below_observe; exact Hbelow |exact Hget] |exact (get_owner Hget)].
    + destruct Hchild as [Htarget Htail].
      set (next_fr := R.with_frame_side fr target (R.accumulated_side_input fr target input)).
      destruct (R.write_side_contribution (R.observe st target) next_fr target (R.accumulated_side_input fr target input)) as [next changed] eqn:Hwrite.
      assert (Hnext : after = R.continue_side next next_fr target tail k changed).
      { unfold step, R.next_config in Hstep; cbn -[R.observe R.write_side_contribution] in Hstep;
          fold next_fr in Hstep; rewrite Hwrite in Hstep; inversion Hstep; reflexivity. }
      subst after; change (owner_phase (R.cfg_control (R.continue_side next next_fr target tail k changed)) (R.frame_owner next_fr) = Some next_phase) in Hnext_phase.
      rewrite phase_continue_side in Hnext_phase; injection Hnext_phase as <-.
      rewrite budget_continue_side in Hbudget; change (round_budget (Sem.support finite) next (R.frame_owner next_fr) (R.frame_phase next_fr) =
        round_budget (Sem.support finite) st (R.frame_owner next_fr) (R.frame_phase next_fr)) in Hbudget.
      rewrite <- (budget_observe (Sem.support finite) st target (R.frame_owner next_fr) (R.frame_phase next_fr)) in Hbudget.
      assert (Hunchanged : changed = false) by (eapply equal_write_unchanged; [exact Hwrite |exact Howner |exact Htarget |exact Hbudget]).
      subst changed; cbn [R.continue_side R.cfg_control R.cfg_state]; split;
        [eapply queue_below_write; [apply queue_below_observe; exact Hbelow |exact Hwrite] |reflexivity].
    + destruct Hchild as [Htarget Htail].
      destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
      * unfold step, R.next_config in Hstep; cbn -[R.observe] in Hstep; rewrite Hmat in Hstep; inversion Hstep; subst after;
          split; [apply queue_below_observe; exact Hbelow |reflexivity].
      * destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target) eqn:Hhigher.
        -- unfold step, R.next_config in Hstep; cbn -[R.observe] in Hstep; rewrite Hmat, Hhigher in Hstep; inversion Hstep; subst after;
             split; [apply queue_below_observe; exact Hbelow |cbn [R.cfg_control R.cfg_state]; auto].
        -- unfold step, R.next_config in Hstep; cbn -[R.observe] in Hstep; rewrite Hmat, Hhigher in Hstep; inversion Hstep; subst after.
           exfalso; assert (Hwas : R.is_materialized st target = true).
           { eapply equal_budget_no_discovery; [exact Hbudget |exact Hlive |exact Htarget |apply materialize_live]. }
           rewrite observe_materialized, Hwas in Hmat; discriminate.
  - subst owner; cbn [control_refs] in Hrefs; destruct Hrefs as [Hfr [Hpending Hk]].
    rewrite phase_dead in Hphase; injection Hphase as <-.
    pose proof (proj1 (ref_owner Hfr)) as Howner.
    destruct pending as [|target pending].
    + unfold step, R.next_config in Hstep; cbn in Hstep; inversion Hstep; subst after; split; [exact Hbelow |reflexivity].
    + inversion Hpending as [|? ? Htarget Htail]; subst; destruct Htarget as [Htarget _].
      destruct (S.mem target (R.frame_current_targets fr)) eqn:Hcurrent.
      * unfold step, R.next_config in Hstep; cbn -[R.write_side_contribution] in Hstep; rewrite Hcurrent in Hstep; inversion Hstep; subst after;
          split; [exact Hbelow |reflexivity].
      * destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite.
        assert (Hnext : after = R.continue_dead next fr direct target pending k changed).
        { unfold step, R.next_config in Hstep; cbn -[R.write_side_contribution] in Hstep; rewrite Hcurrent, Hwrite in Hstep; inversion Hstep; reflexivity. }
        subst after; rewrite phase_continue_dead in Hnext_phase; injection Hnext_phase as <-.
        rewrite budget_continue_dead in Hbudget.
        assert (Hunchanged : changed = false) by (eapply equal_write_unchanged; [exact Hwrite |exact Howner |exact Htarget |exact Hbudget]).
        subst changed; cbn [R.continue_dead R.cfg_control R.cfg_state]; split;
          [eapply queue_below_write; [exact Hbelow |exact Hwrite] |reflexivity].
  - subst owner; rewrite phase_commit in Hphase; injection Hphase as <-.
    destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
    unfold step, R.next_config in Hstep; cbn -[R.set_value] in Hstep; rewrite Hset in Hstep; inversion Hstep; subst after.
    assert (Howner : R.frame_owner next_fr = R.frame_owner fr) by (exact (commit_owner (@commit_footprint st fr direct next next_fr Hset))).
    cbn [R.cfg_control] in Hnext_phase; rewrite <- Howner, phase_drain in Hnext_phase; injection Hnext_phase as <-.
    cbn [R.cfg_state] in Hbudget; rewrite budget_requeue in Hbudget; split; [|exact Howner].
    eapply equal_commit_keeps_lower;
      [exact (@reachable_forward_readers tf roots (configuration st (R.RunCommit fr direct k)) Hreachable)
      |exact Hbelow |exact Hset |exact Hbudget].
  - subst owner; pose proof (drain_lower_returns Hbelow Hstep) as Hreturn.
    assert (Hclosing : closing (configuration st (R.RunDrain fr k)) after (R.frame_owner fr))
      by (exists fr, k; repeat split; auto).
    exfalso; eapply closing_owner_inactive; [eapply reachable_owners_unique; exact Hreachable |exact Hclosing |].
    eapply owner_phase_present; exact Hnext_phase.
Qed.


Theorem episode_quiet_round tf roots (finite : Sem.finite_system tf roots) owner before after phase next_phase :
  reachable tf roots before -> quiet_round (Sem.support finite) owner before ->
  owner_phase (R.cfg_control before) owner = Some phase -> owner_phase (R.cfg_control after) owner = Some next_phase ->
  episode_steps tf owner before after ->
  round_budget (Sem.support finite) (R.cfg_state after) owner next_phase = round_budget (Sem.support finite) (R.cfg_state before) owner phase ->
  quiet_round (Sem.support finite) owner after.
Proof.
  intros Hreachable Hquiet Hphase Hfinal Hpath; revert phase Hreachable Hquiet Hphase; induction Hpath;
    intros phase Hreachable Hquiet Hphase Hbudget; [exact Hquiet |].
  assert (Hnext_reachable := reachable_advance Hreachable H0).
  assert (Hnext_phase : exists p, owner_phase (R.cfg_control next) owner = Some p).
  { destruct (episode_continues_or_done Hpath) as [-> |Hactive]; [exists next_phase; exact Hfinal |].
    exact (@next_owner_phase_exists tf roots before next owner phase Hreachable Hphase H0 Hactive). }
  destruct Hnext_phase as [p Hp].
  pose proof (@next_owner_budget tf roots (Sem.support finite) before next owner phase p Hreachable Hphase Hp H0) as Hnext_budget.
  pose proof (@episode_owner_budget tf roots (Sem.support finite) owner next after p next_phase Hnext_reachable Hp Hfinal Hpath) as Htail_budget.
  assert (Hequal : round_budget (Sem.support finite) (R.cfg_state next) owner p = round_budget (Sem.support finite) (R.cfg_state before) owner phase).
  { apply budget_le_antisym; [exact Hnext_budget |rewrite Hbudget in Htail_budget; exact Htail_budget]. }
  eapply IHHpath; [exact Hfinal |exact Hnext_reachable | |exact Hp |rewrite Hequal; exact Hbudget].
  exact (@next_quiet_round tf roots finite before next owner phase p Hreachable Hquiet Hphase Hp Hequal H0).
Qed.
Lemma lower_drain_no_round tf roots st fr k after phase : reachable tf roots (configuration st (R.RunDrain fr k)) ->
  queue_below st (R.frame_owner fr) -> episode_steps tf (R.frame_owner fr) (configuration st (R.RunDrain fr k)) after ->
  owner_phase (R.cfg_control after) (R.frame_owner fr) = Some phase -> R.cfg_control after <> R.RunDrain fr k -> False.
Proof.
  intros Hreachable Hbelow Hpath Hphase Hdifferent.
  inversion Hpath as [|before next final Hactive Hstep Htail]; subst; [contradiction |].
  pose proof (drain_lower_returns Hbelow Hstep) as Hreturn.
  assert (Hclosing : closing (configuration st (R.RunDrain fr k)) next (R.frame_owner fr)) by (exists fr, k; repeat split; auto).
  assert (Hinactive : ~ In (R.frame_owner fr) (active_owners (R.cfg_control next))).
  { eapply closing_owner_inactive; [eapply reachable_owners_unique; exact Hreachable |exact Hclosing]. }
  destruct (episode_continues_or_done Htail) as [-> |Hin]; [apply Hinactive; eapply owner_phase_present; exact Hphase |contradiction].
Qed.
Theorem round_rerun_paid tf roots (finite : Sem.finite_system tf roots) st fr k committed commit_fr direct drain drain_fr final final_fr :
  reachable tf roots (configuration st (R.RunRhs fr (tf (R.frame_owner fr)) k)) -> queue_below st (R.frame_owner fr) ->
  episode_steps tf (R.frame_owner fr) (configuration st (R.RunRhs fr (tf (R.frame_owner fr)) k))
    (configuration committed (R.RunCommit commit_fr direct k)) ->
  R.frame_owner commit_fr = R.frame_owner fr ->
  step tf (configuration committed (R.RunCommit commit_fr direct k)) (configuration drain (R.RunDrain drain_fr k)) ->
  R.frame_owner drain_fr = R.frame_owner fr ->
  episode_steps tf (R.frame_owner fr) (configuration drain (R.RunDrain drain_fr k))
    (configuration final (R.RunRhs final_fr (tf (R.frame_owner fr)) k)) ->
  R.frame_owner final_fr = R.frame_owner fr ->
  budget_lt (round_budget (Sem.support finite) final (R.frame_owner fr) (R.frame_phase final_fr))
    (round_budget (Sem.support finite) st (R.frame_owner fr) (R.frame_phase fr)).
Proof.
  intros Hreachable Hbelow Hprefix Hcommit_owner Hcommit Hdrain_owner Hsuffix Hfinal_owner.
  assert (Hinitial_phase : owner_phase (R.RunRhs fr (tf (R.frame_owner fr)) k) (R.frame_owner fr) = Some (R.frame_phase fr)) by (apply phase_rhs).
  assert (Hfinal_phase : owner_phase (R.RunRhs final_fr (tf (R.frame_owner fr)) k) (R.frame_owner fr) = Some (R.frame_phase final_fr))
    by (rewrite <- Hfinal_owner; apply phase_rhs).
  assert (Hwhole : episode_steps tf (R.frame_owner fr) (configuration st (R.RunRhs fr (tf (R.frame_owner fr)) k))
    (configuration final (R.RunRhs final_fr (tf (R.frame_owner fr)) k))).
  { eapply episode_append; [exact Hprefix |eapply episode_cons; [cbn [configuration R.cfg_control active_owners]; left; exact Hcommit_owner |exact Hcommit |exact Hsuffix]]. }
  destruct (@episode_owner_budget tf roots (Sem.support finite) (R.frame_owner fr) (configuration st (R.RunRhs fr (tf (R.frame_owner fr)) k)) (configuration final (R.RunRhs final_fr (tf (R.frame_owner fr)) k)) (R.frame_phase fr) (R.frame_phase final_fr) Hreachable Hinitial_phase Hfinal_phase Hwhole) as [Hequal |Hstrict]; [|exact Hstrict].
  assert (Hdrain_reachable : reachable tf roots (configuration drain (R.RunDrain drain_fr k)))
    by (eapply reachable_advance; [eapply reachable_follow; [exact Hreachable |exact (episode_path Hprefix)] |exact Hcommit]).
  assert (Hdrain_phase : owner_phase (R.RunDrain drain_fr k) (R.frame_owner fr) = Some (R.frame_phase drain_fr))
    by (rewrite <- Hdrain_owner; apply phase_drain).
  assert (Hto_drain : episode_steps tf (R.frame_owner fr) (configuration st (R.RunRhs fr (tf (R.frame_owner fr)) k))
    (configuration drain (R.RunDrain drain_fr k))).
  { eapply episode_append; [exact Hprefix |eapply episode_cons; [cbn [configuration R.cfg_control active_owners]; left; exact Hcommit_owner |exact Hcommit |constructor]]. }
  pose proof (@episode_owner_budget tf roots (Sem.support finite) (R.frame_owner fr) (configuration st (R.RunRhs fr (tf (R.frame_owner fr)) k)) (configuration drain (R.RunDrain drain_fr k)) (R.frame_phase fr) (R.frame_phase drain_fr) Hreachable Hinitial_phase Hdrain_phase Hto_drain) as Hfirst.
  pose proof (@episode_owner_budget tf roots (Sem.support finite) (R.frame_owner fr) (configuration drain (R.RunDrain drain_fr k)) (configuration final (R.RunRhs final_fr (tf (R.frame_owner fr)) k)) (R.frame_phase drain_fr) (R.frame_phase final_fr) Hdrain_reachable Hdrain_phase Hfinal_phase Hsuffix) as Hlast.
  assert (Hdrain_equal : round_budget (Sem.support finite) drain (R.frame_owner fr) (R.frame_phase drain_fr) =
    round_budget (Sem.support finite) st (R.frame_owner fr) (R.frame_phase fr)).
  { apply budget_le_antisym; [exact Hfirst |rewrite Hequal in Hlast; exact Hlast]. }
  pose proof (@episode_quiet_round tf roots finite (R.frame_owner fr) (configuration st (R.RunRhs fr (tf (R.frame_owner fr)) k)) (configuration drain (R.RunDrain drain_fr k)) (R.frame_phase fr) (R.frame_phase drain_fr) Hreachable
    ltac:(split; [exact Hbelow |reflexivity]) Hinitial_phase Hdrain_phase Hto_drain Hdrain_equal) as [Hdrain_below _].
  exfalso; eapply lower_drain_no_round;
    [exact Hdrain_reachable |rewrite Hdrain_owner; exact Hdrain_below |rewrite Hdrain_owner; exact Hsuffix
    |rewrite Hdrain_owner; exact Hfinal_phase |discriminate].
Qed.


Lemma episode_finished_path tf before owner k : episode_finished tf before owner k -> episode_complete tf before owner k.
Proof. intros [returned [Hpath Hbelow]]; exists returned; split; [exact (episode_path Hpath) |exact Hbelow]. Qed.
Lemma trace_or_finish tf roots owner base before after : reachable tf roots before ->
  episode_scope owner base (R.cfg_control before) -> steps tf before after ->
  episode_finished tf before owner base \/ (episode_steps tf owner before after /\ episode_scope owner base (R.cfg_control after)).
Proof.
  intros Hreachable Hscope Hpath; revert Hreachable Hscope; induction Hpath; intros Hreachable Hscope.
  - right; split; [constructor |exact Hscope].
  - destruct (@next_episode_scope tf before next owner base Hscope H) as [Hnext |[fr [Hbefore [Howner Hreturn]]]].
    + destruct (IHHpath (reachable_advance Hreachable H) Hnext) as [[returned [Htail Hbelow]] |[Htail Hfinal]].
      * left; exists returned; split; [eapply episode_cons; [eapply episode_scope_active; exact Hscope |exact H |exact Htail] |exact Hbelow].
      * right; split; [eapply episode_cons; [eapply episode_scope_active; exact Hscope |exact H |exact Htail] |exact Hfinal].
    + assert (Hclosing : closing before next owner) by (exists fr, base; repeat split; auto).
      pose proof (closing_queue_below Hreachable H Hclosing) as Hbelow.
      destruct next as [returned ctrl]; cbn [R.cfg_state R.cfg_control] in Hreturn, Hbelow; subst ctrl.
      left; exists returned; split; [eapply episode_cons; [eapply episode_scope_active; exact Hscope |exact H |constructor] |exact Hbelow].
Qed.

Section Rounds.
Variable tf : Syntax.system.
Variable roots : list V.t.
Variable finite : Sem.finite_system tf roots.
Variable owner : V.t.
Hypothesis higher_episodes : forall st child k,
  reachable tf roots (configuration st (R.StartEpisode child k)) -> R.rank_lt st owner child = true ->
  episode_complete tf (configuration st (R.StartEpisode child k)) child k.
Lemma rounds_finish : forall index : nat * (R.state * U.phase), forall fr k,
  R.frame_owner fr = owner -> R.frame_phase fr = snd (snd index) ->
  reachable tf roots (configuration (fst (snd index)) (R.RunRhs fr (tf owner) k)) ->
  (fst index = 0 -> queue_below (fst (snd index)) owner) ->
  episode_complete tf (configuration (fst (snd index)) (R.RunRhs fr (tf owner) k)) owner k.
Proof.
  intro index; induction index as [index IH] using (well_founded_induction (round_order_well_founded (Sem.support finite) owner)).
  destruct index as [flag [st phase]]; intros fr k Howner Hphase Hreachable Hbelow; cbn in Hphase, Hreachable, Hbelow |- *.
  destruct (@rhs_reaches_commit tf roots owner higher_episodes (tf owner) st fr k Howner Hreachable)
    as [committed [commit_fr [direct [Hcommit_owner Heval]]]].
  destruct (@trace_or_finish tf roots owner k _ _ Hreachable ltac:(left; auto) Heval) as [Hdone |[Hprefix Hscope]].
  - apply episode_finished_path; exact Hdone.
  - pose proof (reachable_follow Hreachable Heval) as Hcommit_reachable.
    destruct (R.set_value committed commit_fr direct) as [drained drain_fr] eqn:Hset.
    set (next := R.requeue_changed_controlled_owner committed drained (R.frame_owner commit_fr)).
    assert (Hstep : step tf (configuration committed (R.RunCommit commit_fr direct k)) (configuration next (R.RunDrain drain_fr k))).
    { unfold step, configuration; cbn -[R.set_value]; rewrite Hset; reflexivity. }
    pose proof (reachable_advance Hcommit_reachable Hstep) as Hdrain_reachable.
    assert (Hdrain_owner : R.frame_owner drain_fr = owner)
      by (rewrite (commit_owner (@commit_footprint committed commit_fr direct drained drain_fr Hset)); exact Hcommit_owner).
    destruct (@drain_reaches_boundary tf roots owner higher_episodes (RF.bound (Sem.support finite)) next drain_fr k
      Hdrain_owner Hdrain_reachable (@finite_queue_ceiling tf roots finite next (R.RunDrain drain_fr k) Hdrain_reachable))
      as [boundary [Hdraining [Hboundary_below Hboundary]]].
    destruct (@trace_or_finish tf roots owner k _ _ Hdrain_reachable ltac:(left; auto) Hdraining) as [Hdone |[Hsuffix Hscope_boundary]].
    + destruct (episode_finished_path Hdone) as [returned [Htail Hreturned_below]]; exists returned; split; [|exact Hreturned_below].
      eapply steps_append; [exact Heval |eapply steps_cons; [exact Hstep |exact Htail]].
    + destruct Hboundary as [Hreturn |[final_fr [Hcontrol [Hfinal_owner Hfinal_phase]]]].
      * rewrite Hreturn in Hscope_boundary; exfalso; eapply episode_return_outside; exact Hscope_boundary.
      * destruct boundary as [final ctrl]; cbn [R.cfg_state R.cfg_control] in *; subst ctrl.
        assert (Hdecrease : round_order (Sem.support finite) owner (0,(final,R.frame_phase final_fr)) (flag,(st,phase))).
        { destruct flag as [|flag].
          - unfold round_order; cbn; apply Relation_Operators.right_slex.
            pose proof (@round_rerun_paid tf roots finite st fr k committed commit_fr direct next drain_fr final final_fr
              ltac:(rewrite Howner; exact Hreachable) ltac:(rewrite Howner; apply Hbelow; reflexivity)
              ltac:(rewrite Howner; exact Hprefix) ltac:(rewrite Howner; exact Hcommit_owner)
              Hstep ltac:(rewrite Howner; exact Hdrain_owner) ltac:(rewrite Howner; exact Hsuffix)
              ltac:(rewrite Howner; exact Hfinal_owner)) as Hpaid.
            rewrite Howner, Hphase in Hpaid; exact Hpaid.
          - unfold round_order; cbn; apply Relation_Operators.left_slex; lia. }
        destruct (IH (0,(final,R.frame_phase final_fr)) Hdecrease final_fr k Hfinal_owner eq_refl
          (reachable_follow Hdrain_reachable Hdraining) ltac:(intros _; exact Hboundary_below)) as [returned [Htail Hreturned_below]].
        exists returned; split; [|exact Hreturned_below].
        eapply steps_append; [exact Heval |eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hdraining |exact Htail]]].
Qed.
Theorem episode_finish_from_higher st k : reachable tf roots (configuration st (R.StartEpisode owner k)) ->
  episode_complete tf (configuration st (R.StartEpisode owner k)) owner k.
Proof.
  intro Hreachable; set (first := R.materialize st owner).
  set (fr := R.fresh_frame first owner (U.initial_phase false owner)).
  assert (Hstep : step tf (configuration st (R.StartEpisode owner k)) (configuration first (R.RunRhs fr (tf owner) k))) by reflexivity.
  destruct (@rounds_finish (1,(first,U.initial_phase false owner)) fr k eq_refl eq_refl
    (reachable_advance Hreachable Hstep) ltac:(discriminate)) as [returned [Htail Hbelow]].
  exists returned; split; [eapply steps_cons; eauto |exact Hbelow].
Qed.
End Rounds.


Lemma step_deterministic tf before left right : step tf before left -> step tf before right -> left = right.
Proof. unfold step; congruence. Qed.
Lemma paths_comparable tf start left right : steps tf start left -> steps tf start right ->
  steps tf left right \/ steps tf right left.
Proof.
  intros Hleft; revert right; induction Hleft; intros right Hright; [left; exact Hright |].
  inversion Hright as [|base next_right final Hnext Htail]; subst; [right; eapply steps_cons; eauto |].
  assert (next = next_right) by (eapply step_deterministic; eauto); subst next_right; apply IHHleft; exact Htail.
Qed.
Lemma reachable_rank_unique tf roots left right owner rank_left rank_right : reachable tf roots left -> reachable tf roots right ->
  Ranks.lookup (R.ranking (R.cfg_state left)) owner = Some rank_left ->
  Ranks.lookup (R.ranking (R.cfg_state right)) owner = Some rank_right -> rank_left = rank_right.
Proof.
  intros Hl Hr Hleft Hright; destruct (paths_comparable Hl Hr) as [Hpath |Hpath].
  - pose proof (steps_ranking_extends Hpath Hleft) as Hsame; congruence.
  - pose proof (steps_ranking_extends Hpath Hright) as Hsame; congruence.
Qed.
Theorem finite_episodes_finish tf roots (finite : Sem.finite_system tf roots) : forall st owner k,
  reachable tf roots (configuration st (R.StartEpisode owner k)) -> episode_complete tf (configuration st (R.StartEpisode owner k)) owner k.
Proof.
  assert (Hfinish : forall distance st owner k rank,
    reachable tf roots (configuration st (R.StartEpisode owner k)) -> Ranks.lookup (R.ranking st) owner = Some rank ->
    RF.bound (Sem.support finite) - rank = distance -> episode_complete tf (configuration st (R.StartEpisode owner k)) owner k).
  { intro distance; induction distance using lt_wf_ind; intros st owner k rank Hreachable Hrank Hdistance.
    refine (@episode_finish_from_higher tf roots finite owner _ st k Hreachable).
    intros next child child_k Hchild Hhigher.
    destruct (@lt_ranks (R.ranking next) owner child Hhigher) as [parent_rank [child_rank [Hparent [Hrank_child Hlt]]]].
    assert (Hparent_rank : parent_rank = rank).
    { eapply reachable_rank_unique; [exact Hchild |exact Hreachable |exact Hparent |exact Hrank]. }
    subst parent_rank.
    assert (Hchild_bound : child_rank < RF.bound (Sem.support finite)) by (eapply reachable_rank_bound; [exact Hchild |exact Hrank_child]).
    eapply H with (m := RF.bound (Sem.support finite) - child_rank) (rank := child_rank);
      [lia |exact Hchild |exact Hrank_child |reflexivity]. }
  intros st owner k Hreachable.
  pose proof (@reachable_rank_configuration tf roots (configuration st (R.StartEpisode owner k)) Hreachable) as [_ Hrefs].
  cbn [configuration R.cfg_control R.cfg_state control_refs] in Hrefs; destruct (proj2 (proj1 Hrefs)) as [rank Hrank].
  exact (Hfinish (RF.bound (Sem.support finite) - rank) st owner k rank Hreachable Hrank eq_refl).
Qed.


(** Root seeding and the outer queue share the same drain argument. *)
Definition outer_control remaining := match remaining with
  | None => R.RunLoop | Some roots => R.RunSeedLoop roots end.
Definition outer_stack remaining := match remaining with
  | None => R.KLoop | Some roots => R.KSeedLoop roots end.
Definition outer_done remaining := match remaining with
  | None => R.RunLoop | Some roots => R.RunSeeds roots end.
Lemma outer_drain_finish tf roots (finite : Sem.finite_system tf roots) : forall ceiling st remaining,
  reachable tf roots (configuration st (outer_control remaining)) -> queue_ceiling st ceiling ->
  exists final, steps tf (configuration st (outer_control remaining)) (configuration final (outer_done remaining)) /\ quiescent final.
Proof.
  intro ceiling; induction ceiling using lt_wf_ind; intros st remaining Hreachable Hceiling.
  destruct (R.queue st) as [|head rest] eqn:Hqueue.
  - exists st; split; [|exact Hqueue]; destruct remaining as [remaining |]; [|constructor].
    eapply steps_cons; [unfold step, configuration; cbn [outer_control R.cfg_state R.cfg_control R.next_config R.queue_pop]; rewrite Hqueue; reflexivity |constructor].
  - assert (Hstep : step tf (configuration st (outer_control remaining))
      (configuration (R.with_queue st rest) (R.StartEpisode head (outer_stack remaining)))).
    { destruct remaining; unfold step, configuration; cbn [outer_control outer_stack R.cfg_state R.cfg_control R.next_config R.queue_pop]; rewrite Hqueue; reflexivity. }
    pose proof (reachable_advance Hreachable Hstep) as Hstart.
    destruct (@finite_episodes_finish tf roots finite (R.with_queue st rest) head (outer_stack remaining) Hstart)
      as [returned [Hepisode Hbelow]].
    destruct (Hceiling head ltac:(rewrite Hqueue; left; reflexivity)) as [rank [Hrank Hbound]].
    assert (Hreturned_rank : Ranks.lookup (R.ranking returned) head = Some rank) by (exact (steps_ranking_extends Hepisode Hrank)).
    assert (Hresume : step tf (configuration returned (R.Return (outer_stack remaining))) (configuration returned (outer_control remaining)))
      by (destruct remaining; reflexivity).
    pose proof (reachable_advance (reachable_follow Hstart Hepisode) Hresume) as Hcontinued.
    destruct (H rank Hbound returned remaining Hcontinued (queue_below_ceiling Hbelow Hreturned_rank)) as [final [Htail Hquiet]].
    exists final; split; [eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hepisode |eapply steps_cons; eauto]] |exact Hquiet].
Qed.
Lemma seeds_finish tf roots (finite : Sem.finite_system tf roots) : forall remaining st,
  reachable tf roots (configuration st (R.RunSeeds remaining)) ->
  exists final, steps tf (configuration st (R.RunSeeds remaining)) (terminal final) /\ quiescent final.
Proof.
  intro remaining; induction remaining as [|root remaining IH]; intros st Hreachable.
  - assert (Hstep : step tf (configuration st (R.RunSeeds [])) (configuration st R.RunLoop)) by reflexivity.
    pose proof (reachable_advance Hreachable Hstep) as Hloop.
    destruct (@outer_drain_finish tf roots finite (RF.bound (Sem.support finite)) st None Hloop
      (@finite_queue_ceiling tf roots finite st R.RunLoop Hloop)) as [final [Htail Hquiet]].
    exists final; split; [eapply steps_cons; eauto |exact Hquiet].
  - set (observed := R.observe st root).
    destruct (R.is_materialized observed root) eqn:Hmat.
    + assert (Hstep : step tf (configuration st (R.RunSeeds (root :: remaining))) (configuration observed (R.RunSeeds remaining))).
      { unfold step, configuration; cbn -[R.observe]; fold observed; rewrite Hmat; reflexivity. }
      destruct (IH observed (reachable_advance Hreachable Hstep)) as [final [Htail Hquiet]].
      exists final; split; [eapply steps_cons; eauto |exact Hquiet].
    + assert (Hstep : step tf (configuration st (R.RunSeeds (root :: remaining)))
        (configuration observed (R.StartEpisode root (R.KSeedLoop remaining)))).
      { unfold step, configuration; cbn -[R.observe]; fold observed; rewrite Hmat; reflexivity. }
      pose proof (reachable_advance Hreachable Hstep) as Hstart.
      destruct (@finite_episodes_finish tf roots finite observed root (R.KSeedLoop remaining) Hstart) as [returned [Hepisode Hbelow]].
      assert (Hresume : step tf (configuration returned (R.Return (R.KSeedLoop remaining))) (configuration returned (R.RunSeedLoop remaining))) by reflexivity.
      pose proof (reachable_advance (reachable_follow Hstart Hepisode) Hresume) as Hdrain.
      destruct (@outer_drain_finish tf roots finite (RF.bound (Sem.support finite)) returned (Some remaining) Hdrain
        (@finite_queue_ceiling tf roots finite returned (R.RunSeedLoop remaining) Hdrain)) as [seeded [Houter Hquiet]].
      pose proof (reachable_follow Hdrain Houter) as Hseeded.
      destruct (IH seeded Hseeded) as [final [Htail Hfinal]].
      exists final; split; [|exact Hfinal].
      eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hepisode |eapply steps_cons; [exact Hresume |eapply steps_append; eauto]]].
Qed.
Theorem solver_terminates tf roots : Sem.finite_system tf roots -> exists final, terminates_to tf roots final.
Proof. intro finite; apply (@seeds_finish tf roots finite roots R.empty_state); constructor. Qed.
Theorem finite_fuel_success tf roots : Sem.finite_system tf roots -> exists fuel final, R.solve_fuel fuel tf roots = Some final.
Proof.
  intro finite; apply (proj1 (@termination_iff_fuel tf roots)); exact (solver_terminates finite).
Qed.
Theorem semantic_total_correct tf roots : Sem.finite_system tf roots ->
  exists final, terminates_to tf roots final /\ correct_final_state tf roots final.
Proof.
  intro finite; destruct (solver_terminates finite) as [final Htermination]; exists final; split; [exact Htermination |].
  destruct (termination_has_fuel Htermination) as [fuel Hsuccess].
  exact (@successful_run_correct fuel tf roots final Hsuccess).
Qed.

Definition semantic_termination := solver_terminates.
Definition sufficient_fuel := finite_fuel_success.
Theorem total_correct tf roots : Sem.finite_system tf roots ->
  exists fuel final, R.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final.
Proof.
  intro finite; destruct (sufficient_fuel finite) as [fuel [final Hrun]].
  exists fuel, final; split; [exact Hrun |exact (@successful_run_correct fuel tf roots final Hrun)].
Qed.
Theorem total_least_solution tf roots (finite : Sem.finite_system tf roots) :
  (forall side x phase old input upper, D.leq old upper = true -> D.leq input upper = true ->
    D.leq (snd (U.update side x phase old input)) upper = true) ->
  source_strict_on tf (Sem.support finite) roots -> Sem.system_monotone_on tf (Sem.support finite) ->
  exists fuel final, R.solve_fuel fuel tf roots = Some final /\
    Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
  intros Hbounded Hstrict Hmono; destruct (sufficient_fuel finite) as [fuel [final Hrun]].
  exists fuel, final; split; [exact Hrun |].
  exact (@successful_run_least fuel tf roots finite final Hbounded Hstrict Hmono Hrun).
Qed.


(** The ordinary scheduling argument needs first-discovery policy in addition
    to stable ranks. Keep it optional: termination and correctness also apply
    to stateless ranks. *)
Record first_discovery_laws := {
  discovery_only_target : forall order target next rank variable,
    Ranks.observe order target = (next,rank) -> ranked next variable ->
    variable = target \/ ranked order variable;
  discovery_fresh_above : forall order target next rank owner old_rank,
    RL.valid order -> Ranks.lookup order target = None ->
    Ranks.lookup order owner = Some old_rank ->
    Ranks.observe order target = (next,rank) -> old_rank < rank
}.
Definition all_discovered_live st := forall variable,
  ranked (R.ranking st) variable -> solved st variable.
Definition discovery_ready c := forall variable,
  ranked (R.ranking (R.cfg_state c)) variable ->
  match R.cfg_control c with
  | R.StartEpisode owner _ => variable = owner \/ solved (R.cfg_state c) variable
  | _ => solved (R.cfg_state c) variable
  end.
Section OrdinaryDiscovery.
Variable discovery : first_discovery_laws.

Lemma discovered_observe st target variable : ranked (R.ranking (R.observe st target)) variable ->
  variable = target \/ ranked (R.ranking st) variable.
Proof.
  unfold R.observe; destruct (Ranks.observe (R.ranking st) target) as [order rank] eqn:H;
    cbn; apply (discovery_only_target discovery H).
Qed.
Lemma unseen_higher st owner target : RL.valid (R.ranking st) -> ranked (R.ranking st) owner ->
  all_discovered_live st -> R.is_materialized (R.observe st target) target = false ->
  R.rank_lt (R.observe st target) owner target = true.
Proof.
  intros Hvalid [old_rank Howner] Hlive Hmissing.
  rewrite observe_materialized in Hmissing.
  assert (Hfresh : Ranks.lookup (R.ranking st) target = None).
  { destruct (Ranks.lookup (R.ranking st) target) as [rank|] eqn:Hlookup; auto.
    assert (R.is_materialized st target = true) by
      (apply materialized_iff_solved; apply Hlive; exists rank; exact Hlookup).
    congruence. }
  unfold R.observe, R.rank_lt; destruct (Ranks.observe (R.ranking st) target) as [order rank] eqn:Hobserve; cbn.
  unfold R.ranking_lt; rewrite (@RL.observe_preserves _ _ _ _ _ _ Hobserve Howner),
    (@RL.observe_lookup _ _ _ _ Hobserve); apply Nat.ltb_lt.
  exact (@discovery_fresh_above discovery _ _ _ _ _ _ Hvalid Hfresh Howner Hobserve).
Qed.
Lemma live_same_ranking before after : preserves_live before after ->
  R.ranking after = R.ranking before -> all_discovered_live before -> all_discovered_live after.
Proof. intros Hlive Hr Hall x Hx; apply Hlive, Hall; now rewrite <- Hr. Qed.
Lemma live_observed before after target : preserves_live before after ->
  R.ranking after = R.ranking (R.observe before target) -> all_discovered_live before ->
  solved after target -> all_discovered_live after.
Proof.
  intros Hlive Hr Hall Htarget x Hx; rewrite Hr in Hx;
    destruct (discovered_observe before target Hx) as [->|Hknown]; auto.
Qed.
Lemma next_discovery_ready tf before after : config_wf (fun _ => True) before ->
  ordinary_config before -> discovery_ready before -> step tf before after -> discovery_ready after.
Proof.
  intros [Hstore Hrefs] [_ Hordinary] Hready Hstep.
  pose proof (next_preserves_live Hstep) as Hlive; pose proof Hstep as Hnext.
  unfold discovery_ready in Hready |- *.
  destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in *.
  unfold step, R.next_config in Hnext; cbn [R.cfg_state R.cfg_control] in Hnext.
  destruct ctrl as [|roots|roots|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    cbn [discovery_ready R.cfg_state R.cfg_control control_refs ordinary_control] in Hready, Hrefs, Hordinary.
  - split_program Hnext; intros x Hx; right; apply Hlive, Hready; exact Hx.
  - destruct roots as [|root roots].
    + inversion Hnext; subst; exact Hready.
    + destruct (R.is_materialized (R.observe st root) root) eqn:Hmat; inversion Hnext; subst after.
      * eapply live_observed; [exact Hlive |reflexivity |exact Hready |apply materialized_iff_solved; exact Hmat].
      * intros x Hx; destruct (discovered_observe st root Hx) as [->|Hknown]; [left; reflexivity |right; apply Hlive, Hready; exact Hknown].
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; inversion Hnext; subst after; cbn [discovery_ready R.cfg_state R.cfg_control] in *;
      try exact Hready; intros x Hx; right; apply Hlive, Hready; exact Hx.
  - inversion Hnext; subst after; cbn [discovery_ready R.cfg_state R.cfg_control] in *; intros x Hx; rewrite materialize_rank in Hx.
    destruct (Hready x Hx) as [->|Hknown]; [apply materialize_live |apply Hlive; exact Hknown].
  - destruct Hrefs as [Hfr [_ Hk]]; destruct Hordinary as [_ [Hpure _]].
    assert (Howner : ranked (R.ranking st) (R.frame_owner fr)) by (exact (proj2 (ref_owner Hfr))).
    destruct body as [direct|target tail|target raw tail|target tail].
    + inversion Hnext; subst after; cbn [discovery_ready R.cfg_state R.cfg_control] in *; exact Hready.
    + destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
      * cbn -[R.complete_get] in Hnext; destruct (R.complete_get (R.observe st target) fr target) as [[done next_fr] value] eqn:Hget.
        inversion Hnext; subst after; cbn [discovery_ready R.cfg_state R.cfg_control] in *; eapply live_observed; [exact Hlive |exact (get_rank Hget) |exact Hready |].
        exact (proj2 (preserves_live_get Hget)).
      * rewrite (@unseen_higher st (R.frame_owner fr) target (store_valid Hstore) Howner Hready Hmat) in Hnext; cbn in Hnext.
        inversion Hnext; subst after; cbn [discovery_ready R.cfg_state R.cfg_control] in *; intros x Hx; destruct (discovered_observe st target Hx) as [->|Hknown];
          [left; reflexivity |right; apply Hlive, Hready; exact Hknown].
    + exfalso; exact (pure_no_side Hpure).
    + destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
      * inversion Hnext; subst after; cbn [discovery_ready R.cfg_state R.cfg_control] in *; eapply live_observed; [exact Hlive |reflexivity |exact Hready |].
        apply materialized_iff_solved; exact Hmat.
      * rewrite (@unseen_higher st (R.frame_owner fr) target (store_valid Hstore) Howner Hready Hmat) in Hnext.
        inversion Hnext; subst after; cbn [discovery_ready R.cfg_state R.cfg_control] in *; intros x Hx; destruct (discovered_observe st target Hx) as [->|Hknown];
          [left; reflexivity |right; apply Hlive, Hready; exact Hknown].
  - destruct Hordinary as [_ [-> _]]; inversion Hnext; subst after; cbn [discovery_ready R.cfg_state R.cfg_control] in *; exact Hready.
  - destruct (R.set_value st fr direct) as [done next_fr] eqn:Hset; inversion Hnext; subst after.
    eapply live_same_ranking; [exact Hlive |cbn; apply commit_ranking with (fr := fr) (next_fr := next_fr); apply commit_footprint with (direct := direct); exact Hset |exact Hready].
  - split_program Hnext; cbn [R.cfg_control R.cfg_state] in *; try exact Hready.
    all: try solve [intros x Hx; right; apply Hlive, Hready; exact Hx].
    all: eapply live_same_ranking; [exact Hlive |apply close_rank |exact Hready].
  - destruct k; cbn [ordinary_stack] in Hordinary; try contradiction; split_program Hnext; cbn [R.cfg_control R.cfg_state] in *; try exact Hready.
    eapply live_same_ranking; [exact Hlive |eapply get_rank; eassumption |exact Hready].
Qed.
Theorem ordinary_discovery_ready tf roots c : no_side_effects tf -> reachable tf roots c -> discovery_ready c.
Proof.
  intros Hpure Hpath; assert (Hinitial : discovery_ready (R.initial_config roots)).
  { intros x [rank Hrank]; rewrite RL.empty_lookup in Hrank; discriminate. }
  assert (Hready : forall a b, steps tf a b -> reachable tf roots a -> discovery_ready a -> discovery_ready b).
  { intros a b Hsteps; induction Hsteps; intros Hreachable Hfirst; auto.
    apply IHHsteps; [eapply reachable_advance; eauto |].
    eapply next_discovery_ready; [eapply reachable_rank_configuration; exact Hreachable |
      eapply ordinary_reachable; eauto |exact Hfirst |exact H]. }
  exact (Hready _ _ Hpath (@steps_refl tf (R.initial_config roots)) Hinitial).
Qed.

(** While a newly discovered episode is active, lower owners are suspended.
    Their readers may only watch lower values. Thus changes in this fresh
    region cannot add lower work to the queue. *)
Definition region_readers child st := forall target reader,
  S.mem reader (R.lookup_set (R.readers st) target) = true ->
  R.rank_lt st reader child = true -> R.rank_lt st target child = true.
Definition lower_queue_inclusion child before after := forall variable,
  R.rank_lt after variable child = true -> In variable (R.queue after) -> In variable (R.queue before).
Lemma lower_reflect_observe st child target variable : RL.valid (R.ranking st) ->
  ranked (R.ranking st) child -> R.rank_lt (R.observe st target) variable child = true -> R.rank_lt st variable child = true.
Proof.
  intros Hvalid [child_rank Hchild] Hlower.
  destruct (@lt_ranks (R.ranking (R.observe st target)) variable child Hlower)
    as [rank [rank' [Hv [Hc Hlt]]]].
  pose proof (@observe_extends st target child child_rank Hchild) as Hc'; rewrite Hc' in Hc; inversion Hc; subst rank'.
  destruct (discovered_observe st target (ex_intro _ rank Hv)) as [Heq |[old Hbefore]].
  - subst variable; destruct (Ranks.lookup (R.ranking st) target) as [old|] eqn:Hbefore.
    + pose proof (@observe_extends st target target old Hbefore) as Hafter; rewrite Hafter in Hv; inversion Hv; subst old.
      unfold R.rank_lt, R.ranking_lt; rewrite Hbefore, Hchild; apply Nat.ltb_lt; exact Hlt.
    + unfold R.observe in Hv; destruct (Ranks.observe (R.ranking st) target) as [order fresh] eqn:Hobserve; cbn in Hv.
      pose proof (@RL.observe_lookup _ _ _ _ Hobserve) as Htarget; rewrite Htarget in Hv; inversion Hv; subst fresh.
      pose proof (@discovery_fresh_above discovery _ _ _ _ _ _ Hvalid Hbefore Hchild Hobserve); lia.
  - pose proof (@observe_extends st target variable old Hbefore) as Hafter; rewrite Hafter in Hv; inversion Hv; subst old.
    unfold R.rank_lt, R.ranking_lt; rewrite Hbefore, Hchild; apply Nat.ltb_lt; exact Hlt.
Qed.
Lemma region_layout child before after : R.ranking after = R.ranking before ->
  R.readers after = R.readers before -> region_readers child before -> region_readers child after.
Proof. intros Hr Hread H target reader Hmem Hlt; unfold R.rank_lt in *; rewrite Hr in *; rewrite Hread in Hmem; eauto. Qed.
Lemma region_observe child st target : RL.valid (R.ranking st) -> ranked (R.ranking st) child ->
  region_readers child st -> region_readers child (R.observe st target).
Proof.
  intros Hvalid Hchild H observed reader Hmem Hlt.
  assert (Hread : R.readers (R.observe st target) = R.readers st) by (unfold R.observe; destruct (Ranks.observe _ _); reflexivity).
  rewrite Hread in Hmem; apply lt_extends with (before := R.ranking st); [apply observe_extends |].
  apply H with (reader := reader); [exact Hmem |eapply lower_reflect_observe; eauto].
Qed.
Lemma region_get child st fr target next next_fr value :
  ~ R.rank_lt st (R.frame_owner fr) child = true -> region_readers child st ->
  R.complete_get st fr target = (next,next_fr,value) -> region_readers child next.
Proof.
  intros Howner Hread Hget; unfold R.complete_get in Hget; destruct (R.rank_lt st (R.frame_owner fr) target);
    inversion Hget; subst next next_fr value; intros observed reader Hmem Hlt;
    rewrite materialize_readers in Hmem;
    unfold R.rank_lt in Hlt |- *; rewrite materialize_rank in Hlt |- *;
    cbn [R.rank_lt R.ranking R.with_readers R.promote_controlled R.with_controlled] in Hlt |- *;
    unfold R.lookup_set in Hmem; cbn [R.readers R.with_readers R.promote_controlled R.with_controlled] in Hmem;
    destruct (V.eq_dec observed target) as [->|Hneq].
  all: try solve [rewrite ML.lookup_update_same in Hmem; apply SL.add_spec in Hmem; destruct Hmem as [->|Hmem];
    [exfalso; apply Howner; exact Hlt |apply Hread with (reader := reader); assumption]].
  all: rewrite ML.lookup_update_other in Hmem by assumption;
    apply Hread with (reader := reader); assumption.
Qed.
Lemma region_commit child st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  region_readers child st -> region_readers child next.
Proof.
  intros Hset Hread; unfold R.set_value in Hset; split_program Hset; try exact Hread.
  all: intros target reader Hmem Hlt;
    cbn [R.with_readers R.with_queue R.with_sigma R.readers R.ranking R.rank_lt] in *;
    unfold R.lookup_set in Hmem; destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq].
  all: try solve [rewrite ML.lookup_update_same, SL.empty_spec in Hmem; discriminate].
  all: rewrite ML.lookup_update_other in Hmem by assumption; apply Hread with (reader := reader); assumption.
Qed.
Lemma lower_queue_layout child before after : R.ranking after = R.ranking before ->
  (forall x, In x (R.queue after) -> In x (R.queue before)) -> lower_queue_inclusion child before after.
Proof. intros _ H x _; apply H. Qed.
Lemma lower_queue_commit child st fr direct next next_fr :
  ~ R.rank_lt st (R.frame_owner fr) child = true -> region_readers child st ->
  R.set_value st fr direct = (next,next_fr) -> lower_queue_inclusion child st next.
Proof.
  intros Howner Hread Hset; unfold R.set_value in Hset; split_program Hset; intros x Hlower Hin; try exact Hin.
  all: cbn [R.with_readers R.with_queue R.with_sigma R.queue R.ranking R.rank_lt R.enqueue_all] in *;
    apply insert_all_members in Hin; destruct Hin as [Hnew|Hin]; [|exact Hin].
  all: exfalso; apply Howner; apply Hread with (reader := x); [apply SL.mem_spec; exact Hnew |exact Hlower].
Qed.
Lemma lower_queue_requeue child before after owner : R.ranking after = R.ranking before ->
  ~ R.rank_lt before owner child = true -> lower_queue_inclusion child before after ->
  lower_queue_inclusion child before (R.requeue_changed_controlled_owner before after owner).
Proof.
  intros Hr Howner Hq; unfold R.requeue_changed_controlled_owner.
  destruct (Features.recompute_controlled && S.mem owner (R.controlled before) &&
    negb (R.equivalent (R.sigma_value after owner) (R.sigma_value before owner)))%bool; [|exact Hq].
  intros x Hlower Hin; unfold R.enqueue in Hin; cbn [R.with_queue R.queue] in Hin.
  apply insert_members in Hin; destruct Hin as [->|Hin]; [|apply Hq; assumption].
  exfalso; apply Howner; unfold R.rank_lt in *; cbn [R.ranking R.with_queue] in Hlower; now rewrite Hr in Hlower.
Qed.
Lemma ordered_head_not_lower order head rest child : ordered order (head :: rest) ->
  In child (head :: rest) -> ~ R.ranking_lt order head child = true.
Proof.
  intros Hordered Hin Hlower; destruct (V.eq_dec child head) as [->|Hneq].
  - rewrite lt_irrefl in Hlower; discriminate.
  - pose proof (@ordered_member_lower
      (R.with_ranking R.empty_state order) head rest child Hordered Hin Hneq) as Hhigher.
    pose proof (@lt_trans order head child head Hlower Hhigher) as Hcycle; rewrite lt_irrefl in Hcycle; discriminate.
Qed.

Definition region_transition child before after :=
  region_readers child after /\ lower_queue_inclusion child before after /\
  forall x, R.rank_lt after x child = true -> R.rank_lt before x child = true.
Lemma region_static child before after : R.ranking after = R.ranking before ->
  R.readers after = R.readers before -> (forall x, In x (R.queue after) -> In x (R.queue before)) ->
  region_readers child before -> region_transition child before after.
Proof.
  intros Hr Hread Hq H; split; [eapply region_layout; eauto |]; split.
  - apply lower_queue_layout; auto.
  - intros x Hlt; unfold R.rank_lt in *; now rewrite Hr in Hlt.
Qed.
Lemma region_observed child st target : RL.valid (R.ranking st) -> ranked (R.ranking st) child ->
  region_readers child st -> region_transition child st (R.observe st target).
Proof.
  intros Hvalid Hchild H; split; [apply region_observe; auto |]; split.
  - intros x _ Hin; unfold R.observe in Hin; destruct (Ranks.observe _ _); exact Hin.
  - intros x Hlt; eapply lower_reflect_observe; eauto.
Qed.
Lemma region_trans child a b c : region_transition child a b -> region_transition child b c -> region_transition child a c.
Proof.
  intros [_ [Hab Hba]] [Hread [Hbc Hcb]]; split; [exact Hread |]; split.
  - intros x Hlt Hin; apply Hab; [apply Hcb; exact Hlt |apply Hbc; assumption].
  - intros x Hlt; apply Hba, Hcb; exact Hlt.
Qed.
Lemma region_get_transition child st fr target next next_fr value :
  ~ R.rank_lt st (R.frame_owner fr) child = true -> region_readers child st ->
  R.complete_get st fr target = (next,next_fr,value) -> region_transition child st next.
Proof.
  intros Howner Hread Hget; split; [eapply region_get; eauto |]; split.
  - intros x _ Hin; rewrite (proj1 (proj2 (get_layout Hget))) in Hin; exact Hin.
  - intros x Hlt; unfold R.rank_lt in *; now rewrite (get_rank Hget) in Hlt.
Qed.
Lemma pop_subset q head rest : R.queue_pop q = Some (head,rest) -> forall x, In x rest -> In x q.
Proof. destruct q as [|first tail]; cbn; intro H; [discriminate |inversion H; subst; auto]. Qed.

Lemma next_region tf before after child : config_wf (fun _ => True) before ->
  ordinary_config before -> discovery_ready before -> active_ordered before ->
  In child (active_owners (R.cfg_control before)) -> region_readers child (R.cfg_state before) ->
  step tf before after -> region_transition child (R.cfg_state before) (R.cfg_state after).
Proof.
  intros [Hstore Hrefs] [_ Hordinary] Hready Hordered Hactive Hread Hstep.
  assert (Hchild : ranked (R.ranking (R.cfg_state before)) child).
  { pose proof (@active_references (known (fun _ => True) (R.cfg_state before)) (fun _ => True) (R.cfg_control before) Hrefs) as Hknown; rewrite Forall_forall in Hknown.
    exact (proj2 (Hknown child Hactive)). }
  destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in *;
    unfold active_ordered in Hordered; cbn [R.cfg_state R.cfg_control] in Hordered.
  unfold discovery_ready in Hready; cbn [R.cfg_state R.cfg_control] in Hready.
  unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl as [|roots|roots|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    cbn [R.cfg_control active_owners ordinary_control control_refs] in Hordered, Hactive, Hordinary, Hrefs; try contradiction.
  all: try assert (Howner : ~ R.rank_lt st (R.frame_owner fr) child = true)
    by (apply (ordered_head_not_lower Hordered Hactive)).
  - inversion Hstep; subst after; cbn [R.cfg_state]; eapply region_static with (before := st);
      [apply materialize_rank |apply materialize_readers |intros x Hin; rewrite materialize_queue in Hin; exact Hin |exact Hread].
  - destruct Hordinary as [_ [Hpure _]]; destruct Hrefs as [Hfr [_ Hk]].
    assert (Hrank : ranked (R.ranking st) (R.frame_owner fr)) by (exact (proj2 (ref_owner Hfr))).
    destruct body as [direct|target tail|target raw tail|target tail].
    + inversion Hstep; subst after; cbn [R.cfg_state]; eapply region_static; eauto.
    + pose proof (@region_observed child st target (store_valid Hstore) Hchild Hread) as Hobserved.
      destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
      * cbn -[R.complete_get] in Hstep; destruct (R.complete_get (R.observe st target) fr target) as [[done next_fr] value] eqn:Hget.
        inversion Hstep; subst after; cbn [R.cfg_state]; eapply region_trans; [exact Hobserved |].
        eapply region_get_transition; [|exact (proj1 Hobserved) |exact Hget].
        intro Hlower; apply Howner; exact (@lower_reflect_observe st child target (R.frame_owner fr) (store_valid Hstore) Hchild Hlower).
      * rewrite (@unseen_higher st (R.frame_owner fr) target (store_valid Hstore) Hrank Hready Hmat) in Hstep; cbn in Hstep.
        inversion Hstep; subst after; cbn [R.cfg_state]; exact Hobserved.
    + exfalso; exact (pure_no_side Hpure).
    + pose proof (@region_observed child st target (store_valid Hstore) Hchild Hread) as Hobserved.
      destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
      * inversion Hstep; subst after; cbn [R.cfg_state]; exact Hobserved.
      * rewrite (@unseen_higher st (R.frame_owner fr) target (store_valid Hstore) Hrank Hready Hmat) in Hstep.
        inversion Hstep; subst after; cbn [R.cfg_state]; exact Hobserved.
  - destruct Hordinary as [_ [-> _]]; inversion Hstep; subst after; cbn [R.cfg_state]; eapply region_static with (before := st); eauto.
  - destruct (R.set_value st fr direct) as [done next_fr] eqn:Hset; inversion Hstep; subst after.
    pose proof (@commit_footprint st fr direct done next_fr Hset) as Hview.
    split; [eapply region_layout with (before := done); [reflexivity |reflexivity |eapply region_commit; eauto] |]; split.
    + eapply lower_queue_requeue; [exact (commit_ranking Hview) |exact Howner |eapply lower_queue_commit; eauto].
    + intros x Hlt; unfold R.rank_lt in *; cbn [R.cfg_state R.requeue_changed_controlled_owner R.with_queue R.ranking] in Hlt.
      now rewrite (commit_ranking Hview) in Hlt.
  - split_program Hstep; cbn [R.cfg_state];
      try solve [eapply region_static with (before := st); [reflexivity |reflexivity |eapply pop_subset; eassumption |exact Hread]].
    all: eapply region_static with (before := st); [apply close_rank | |intros x Hin; rewrite close_queue in Hin; exact Hin |exact Hread].
    all: unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity.
  - destruct k; cbn [suspended_owners ordinary_stack] in Hactive, Hordinary, Hordered; try contradiction.
    all: try assert (Howner : ~ R.rank_lt st (R.frame_owner f) child = true)
      by (apply (ordered_head_not_lower Hordered Hactive)).
    + destruct (R.complete_get st f t) as [[done next_fr] value] eqn:Hget.
      inversion Hstep; subst after; cbn [R.cfg_state]; eapply region_get_transition; eauto.
    + inversion Hstep; subst after; cbn [R.cfg_state]; eapply region_static with (before := st); eauto.
    + inversion Hstep; subst after; cbn [R.cfg_state]; eapply region_static with (before := st); eauto.
Qed.
Lemma fresh_above_known st child variable : RL.valid (R.ranking st) ->
  Ranks.lookup (R.ranking st) child = None -> ranked (R.ranking st) variable ->
  R.rank_lt (R.observe st child) variable child = true.
Proof.
  intros Hvalid Hfresh [rank Hknown]; unfold R.observe, R.rank_lt;
    destruct (Ranks.observe (R.ranking st) child) as [order child_rank] eqn:Hobserve; cbn.
  unfold R.ranking_lt; rewrite (@RL.observe_preserves _ _ _ _ _ _ Hobserve Hknown),
    (@RL.observe_lookup _ _ _ _ Hobserve); apply Nat.ltb_lt.
  exact (@discovery_fresh_above discovery _ _ _ _ _ _ Hvalid Hfresh Hknown Hobserve).
Qed.
Lemma region_at_discovery st child : store_wf (fun _ => True) st ->
  Ranks.lookup (R.ranking st) child = None -> region_readers child (R.observe st child).
Proof.
  intros Hstore Hfresh target reader Hmem _.
  assert (Hread : R.readers (R.observe st child) = R.readers st) by (unfold R.observe; destruct (Ranks.observe _ _); reflexivity).
  rewrite Hread in Hmem; unfold R.lookup_set in Hmem; destruct (M.lookup (R.readers st) target) as [watchers|] eqn:Hlookup.
  - apply fresh_above_known; [exact (store_valid Hstore) |exact Hfresh |].
    exact (proj2 (proj1 (refs_readers (store_references Hstore) Hlookup))).
  - rewrite SL.empty_spec in Hmem; discriminate.
Qed.
Definition queue_gap st parent child := forall x, In x (R.queue st) ->
  R.rank_lt st x child = true -> R.rank_lt st x parent = true.
Inductive pending_frontier parent k c : Prop :=
| Build_pending_frontier child :
  region_readers child (R.cfg_state c) ->
  queue_gap (R.cfg_state c) parent child ->
  (episode_scope child k (R.cfg_control c) \/ R.cfg_control c = R.Return k) ->
  (R.cfg_control c = R.Return k -> queue_below (R.cfg_state c) child) ->
  pending_frontier parent k c.
Lemma pending_returns parent k st : pending_frontier parent k (configuration st (R.Return k)) -> queue_below st parent.
Proof.
  intros [child Hread Hgap Hscope Hboundary]; unfold queue_below; rewrite Forall_forall; intros x Hin.
  apply Hgap; [exact Hin |]; specialize (Hboundary eq_refl); unfold queue_below in Hboundary;
    rewrite Forall_forall in Hboundary; apply Hboundary; exact Hin.
Qed.
Lemma next_pending_frontier tf roots parent k before after : no_side_effects tf -> reachable tf roots before ->
  pending_frontier parent k before -> R.cfg_control before <> R.Return k -> step tf before after ->
  pending_frontier parent k after.
Proof.
  intros Hpure Hreachable [child Hread Hgap [Hscope|Hreturned] Hboundary] Hnot Hstep; [|contradiction].
  pose proof (@next_region tf before after child
    (@reachable_rank_configuration tf roots before Hreachable)
    (@ordinary_reachable tf roots before Hpure Hreachable)
    (@ordinary_discovery_ready tf roots before Hpure Hreachable)
    (@reachable_active_ordered tf roots before Hreachable)
    (@episode_scope_active child k (R.cfg_control before) Hscope) Hread Hstep) as [Hread' [Hq Hreflect]].
  destruct (@next_episode_scope tf before after child k Hscope Hstep) as [Hscope'|[fr [Hbefore [Howner Hreturn]]]].
  - refine (@Build_pending_frontier parent k after child Hread' _ (or_introl Hscope') _).
    + intros x Hin Hlt; apply lt_extends with (before := R.ranking (R.cfg_state before)); [eapply next_ranking_extends; exact Hstep |].
      apply Hgap; [apply Hq; assumption |apply Hreflect; exact Hlt].
    + intro Hreturn; rewrite Hreturn in Hscope'; exfalso; exact (@episode_return_outside child k Hscope').
  - refine (@Build_pending_frontier parent k after child Hread' _ (or_intror Hreturn) _).
    + intros x Hin Hlt; apply lt_extends with (before := R.ranking (R.cfg_state before)); [eapply next_ranking_extends; exact Hstep |].
      apply Hgap; [apply Hq; assumption |apply Hreflect; exact Hlt].
    + intros _; apply (closing_queue_below Hreachable Hstep); exists fr, k; repeat split; auto.
Qed.
Fixpoint stack_frontiers c k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => True
  | R.KAfterGet fr _ _ rest | R.KAfterSpawn fr _ rest =>
      inhabited (pending_frontier (R.frame_owner fr) k c) /\ stack_frontiers c rest
  | R.KDrain _ rest => stack_frontiers c rest
  | R.KAfterSide _ _ _ | R.KDead _ _ _ _ => False
  end.
Definition frontier_stack c :=
  match R.cfg_control c with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
  | R.StartEpisode _ k | R.RunRhs _ _ k | R.RunDead _ _ _ k | R.RunCommit _ _ k
  | R.RunDrain _ k | R.Return k => stack_frontiers c k
  end.
Lemma next_stack_frontiers tf roots before after k : no_side_effects tf -> reachable tf roots before ->
  step tf before after -> stack_frontiers before k ->
  (match R.cfg_control before with R.Return returned => stack_depth k < stack_depth returned | _ => True end) ->
  stack_frontiers after k.
Proof.
  intros Hpure Hreachable Hstep; induction k; cbn [stack_frontiers stack_depth]; intros Hfront Hdepth; try contradiction; auto.
  all: try solve [apply IHk; [exact Hfront |destruct (R.cfg_control before); cbn in *; auto; lia]].
  all: destruct Hfront as [[Hpending] Hrest]; split.
  all: try solve [apply IHk; [exact Hrest |destruct (R.cfg_control before); cbn in *; auto; lia]].
  all: constructor; eapply next_pending_frontier; [exact Hpure |exact Hreachable |exact Hpending | |exact Hstep].
  all: intro Hreturn; rewrite Hreturn in Hdepth; cbn [stack_depth] in Hdepth; lia.
Qed.
Definition current_frontier c :=
  match R.cfg_control c with
  | R.RunSeeds _ => quiescent (R.cfg_state c)
  | R.StartEpisode owner _ => queue_below (R.cfg_state c) owner
  | R.RunRhs fr _ _ | R.RunDead fr _ _ _ | R.RunCommit fr _ _ => queue_below (R.cfg_state c) (R.frame_owner fr)
  | _ => True
  end.
Definition ordinary_frontier c := current_frontier c /\ frontier_stack c.
Lemma unmaterialized_unseen st target : all_discovered_live st ->
  R.is_materialized (R.observe st target) target = false -> Ranks.lookup (R.ranking st) target = None.
Proof.
  intros Hlive Hmat; rewrite observe_materialized in Hmat; destruct (Ranks.lookup (R.ranking st) target) as [rank|] eqn:Hlookup; auto.
  assert (R.is_materialized st target = true) by (apply materialized_iff_solved, Hlive; exists rank; exact Hlookup); congruence.
Qed.
Lemma pending_fresh st parent child k : store_wf (fun _ => True) st -> Ranks.lookup (R.ranking st) child = None ->
  queue_below st parent -> pending_frontier parent k (configuration (R.observe st child) (R.StartEpisode child k)).
Proof.
  intros Hstore Hfresh Hbelow; refine (@Build_pending_frontier parent k (configuration (R.observe st child) (R.StartEpisode child k)) child (region_at_discovery Hstore Hfresh) _ _ _).
  - intros x Hin _; cbn [configuration R.cfg_state] in Hin |- *; rewrite observe_queue in Hin; eapply lt_extends; [apply observe_extends |].
    unfold queue_below in Hbelow; rewrite Forall_forall in Hbelow; apply Hbelow; exact Hin.
  - left; left; auto.
  - discriminate.
Qed.
Lemma popped_queue_below st head rest : ordered (R.ranking st) (R.queue st) ->
  R.queue_pop (R.queue st) = Some (head,rest) -> queue_below (R.with_queue st rest) head.
Proof.
  intros Hordered Hpop; destruct (R.queue st) as [|first tail] eqn:Hq; cbn [R.queue_pop] in Hpop; [discriminate |].
  inversion Hpop; subst first tail; exact (proj2 (ordered_tail Hordered)).
Qed.

Theorem next_ordinary_frontier tf roots before after : no_side_effects tf -> reachable tf roots before ->
  ordinary_frontier before -> step tf before after -> ordinary_frontier after.
Proof.
  intros Hpure Hreachable [Hcurrent Hstack] Hstep.
  pose proof (@reachable_rank_configuration tf roots before Hreachable) as [Hstore Hrefs].
  pose proof (@ordinary_reachable tf roots before Hpure Hreachable) as [_ Hordinary].
  pose proof (@ordinary_discovery_ready tf roots before Hpure Hreachable) as Hready.
  assert (Hkeep : forall k, stack_frontiers before k ->
    (match R.cfg_control before with R.Return returned => stack_depth k < stack_depth returned | _ => True end) ->
    stack_frontiers after k) by (intros; eapply next_stack_frontiers; eauto).
  destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in *.
  unfold current_frontier in Hcurrent; unfold frontier_stack in Hstack;
    unfold discovery_ready in Hready; cbn [R.cfg_state R.cfg_control] in Hcurrent, Hstack, Hready, Hkeep.
  unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  unfold ordinary_frontier, current_frontier, frontier_stack.
  destruct ctrl as [|seeds|seeds|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    cbn [R.cfg_control control_refs ordinary_control] in Hrefs, Hordinary, Hcurrent, Hstack, Hready, Hkeep.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|] eqn:Hpop; [|discriminate].
    inversion Hstep; subst after; split; [eapply popped_queue_below; [exact (store_ordered Hstore) |exact Hpop] |exact I].
  - destruct seeds as [|root seeds].
    + inversion Hstep; subst after; auto.
    + destruct (R.is_materialized (R.observe st root) root); inversion Hstep; subst after; split; try exact I.
      all: unfold queue_below, quiescent; cbn [R.cfg_state R.cfg_control]; rewrite observe_queue, Hcurrent; constructor.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|] eqn:Hpop; inversion Hstep; subst after; split; try exact I.
    + eapply popped_queue_below; [exact (store_ordered Hstore) |exact Hpop].
    + unfold quiescent; cbn [R.cfg_state]; destruct (R.queue st); cbn [R.queue_pop] in Hpop; [reflexivity |discriminate].
  - inversion Hstep; subst after; split.
    + eapply (@queue_below_layout st (R.materialize st owner) owner); [apply materialize_queue |rewrite materialize_rank; apply extends_refl |exact Hcurrent].
    + apply Hkeep; [exact Hstack |exact I].
  - destruct Hrefs as [Hfr [_ Hk]]; destruct Hordinary as [_ [Hcode _]].
    assert (Howner : ranked (R.ranking st) (R.frame_owner fr)) by (exact (proj2 (ref_owner Hfr))).
    destruct body as [direct|target tail|target raw tail|target tail].
    + inversion Hstep; subst after; split; [exact Hcurrent |apply Hkeep; [exact Hstack |exact I]].
    + destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
      * cbn -[R.complete_get] in Hstep; destruct (R.complete_get (R.observe st target) fr target) as [[done next_fr] value] eqn:Hget.
        inversion Hstep; subst after; split.
        -- cbn [R.cfg_state R.cfg_control]; rewrite (get_owner Hget); eapply queue_below_get; [apply queue_below_observe; exact Hcurrent |exact Hget].
        -- apply Hkeep; [exact Hstack |exact I].
      * pose proof (@unseen_higher st (R.frame_owner fr) target (store_valid Hstore) Howner Hready Hmat) as Hhigher.
        rewrite Hhigher in Hstep; cbn in Hstep; inversion Hstep; subst after; split.
        -- cbn [R.cfg_state R.cfg_control]; unfold queue_below; rewrite observe_queue;
            eapply Forall_impl; [intros x Hx; eapply lt_trans; [eapply lt_extends; [apply observe_extends |exact Hx] |exact Hhigher] |exact Hcurrent].
        -- cbn [R.cfg_control stack_frontiers]; split; [constructor; apply pending_fresh; [exact Hstore |eapply unmaterialized_unseen; eauto |exact Hcurrent] |apply Hkeep; [exact Hstack |exact I]].
    + exfalso; exact (pure_no_side Hcode).
    + destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
      * inversion Hstep; subst after; split; [apply queue_below_observe; exact Hcurrent |apply Hkeep; [exact Hstack |exact I]].
      * pose proof (@unseen_higher st (R.frame_owner fr) target (store_valid Hstore) Howner Hready Hmat) as Hhigher.
        rewrite Hhigher in Hstep; inversion Hstep; subst after; split.
        -- cbn [R.cfg_state R.cfg_control]; unfold queue_below; rewrite observe_queue;
            eapply Forall_impl; [intros x Hx; eapply lt_trans; [eapply lt_extends; [apply observe_extends |exact Hx] |exact Hhigher] |exact Hcurrent].
        -- cbn [R.cfg_control stack_frontiers]; split; [constructor; apply pending_fresh; [exact Hstore |eapply unmaterialized_unseen; eauto |exact Hcurrent] |apply Hkeep; [exact Hstack |exact I]].
  - destruct Hordinary as [_ [-> _]]; inversion Hstep; subst after; split; [exact Hcurrent |apply Hkeep; [exact Hstack |exact I]].
  - destruct (R.set_value st fr direct) as [done next_fr]; inversion Hstep; subst after; split; [exact I |apply Hkeep; [exact Hstack |exact I]].
  - split_program Hstep.
    all: repeat match goal with Hp : R.queue_pop ?q = Some (?head,?rest), Hpeek : R.queue_peek ?q = Some ?next |- _ =>
      let Hsame := fresh "peek_pop" in pose proof (@peek_popped q head rest Hp) as Hsame;
      rewrite Hpeek in Hsame; inversion Hsame; subst head; clear Hpeek Hsame end.
    all: cbn [R.cfg_state R.cfg_control R.frame_owner R.fresh_frame stack_frontiers]; split.
    all: try exact I.
    all: try solve [apply Hkeep; [exact Hstack |exact I]].
    all: eapply popped_queue_below; [exact (store_ordered Hstore) |eassumption].
  - destruct k; cbn [stack_frontiers] in Hstack.
    + inversion Hstep; subst after; auto.
    + inversion Hstep; subst after; auto.
    + destruct Hstack as [[Hpending] Hrest]; destruct (R.complete_get st f t) as [[done next_fr] value] eqn:Hget.
      inversion Hstep; subst after; split.
      * cbn [R.cfg_state R.cfg_control]; rewrite (get_owner Hget); eapply queue_below_get; [eapply pending_returns; exact Hpending |exact Hget].
      * apply Hkeep; [exact Hrest |cbn [stack_depth]; lia].
    + contradiction.
    + destruct Hstack as [[Hpending] Hrest]; inversion Hstep; subst after; split.
      * eapply pending_returns; exact Hpending.
      * apply Hkeep; [exact Hrest |cbn [stack_depth]; lia].
    + contradiction.
    + inversion Hstep; subst after; split; [exact I |apply Hkeep; [exact Hstack |cbn [stack_depth]; lia]].
Qed.
Theorem ordinary_frontiers tf roots c : no_side_effects tf -> reachable tf roots c -> ordinary_frontier c.
Proof.
  intros Hpure Hpath; assert (Hinitial : ordinary_frontier (R.initial_config roots)) by (split; [reflexivity |exact I]).
  assert (Hpreserve : forall a b, steps tf a b -> reachable tf roots a -> ordinary_frontier a -> ordinary_frontier b).
  { intros a b Hsteps; induction Hsteps; intros Hreachable Hfirst; auto.
    apply IHHsteps; [eapply reachable_advance; eauto |eapply next_ordinary_frontier; eauto]. }
  exact (Hpreserve _ _ Hpath (@steps_refl tf (R.initial_config roots)) Hinitial).
Qed.
Corollary ordinary_evaluation_queue_below tf roots st fr body k : no_side_effects tf ->
  reachable tf roots (configuration st (R.RunRhs fr body k)) -> queue_below st (R.frame_owner fr).
Proof. intros Hpure Hreachable; exact (proj1 (@ordinary_frontiers tf roots _ Hpure Hreachable)). Qed.
Corollary ordinary_commit_queue_below tf roots st fr direct k : no_side_effects tf ->
  reachable tf roots (configuration st (R.RunCommit fr direct k)) -> queue_below st (R.frame_owner fr).
Proof. intros Hpure Hreachable; exact (proj1 (@ordinary_frontiers tf roots _ Hpure Hreachable)). Qed.

Record closed_observation body st result : Prop := {
  closed_at : Sem.observes_at (R.sigma_value st) body result;
  closed_reads : forall target value, In (target,value) (Sem.observed_reads result) -> solved st target;
  closed_spawns : forall target, In target (Sem.observed_spawns result) -> solved st target
}.
Lemma closed_replay body st result : closed_observation body st result ->
  replay st body (Sem.observed_direct result) (Sem.observed_reads result) (Sem.observed_sides result).
Proof.
  intros [[Htrace Hvalues] Hreads Hspawns]; apply observation_replay; [exact Htrace |].
  intros target value Hin; destruct (Hreads target value Hin) as [actual Hlookup].
  rewrite (Hvalues target value Hin), (@read_value st target actual Hlookup); exact Hlookup.
Qed.
Lemma closed_post tf st owner result : no_side_effects tf -> closed_observation (tf owner) st result ->
  D.leq (Sem.observed_direct result) (R.sigma_value st owner) = true -> owner_post_solution tf st owner.
Proof.
  intros Hpure Hclosed Hdirect; pose proof (closed_replay Hclosed) as Hreplay; split.
  - eexists _, _, _; exact Hreplay.
  - split.
    + intros direct reads effects Hother; destruct (replay_observation Hother) as [other [Hat [Hd [Hr He]]]].
      assert (Heq : result = other) by (eapply observation_unique; [exact (closed_at Hclosed) |exact Hat]); subst other.
      rewrite <- Hd, <- He; split; [exact Hdirect |].
      intros target raw Hin; assert (Hempty : Sem.observed_sides result = []) by (exact (Hpure owner result (proj1 (closed_at Hclosed)))).
      rewrite Hempty in Hin; contradiction.
    + intros other Hat target Hin.
      assert (Heq : result = other) by (eapply observation_unique; [exact (closed_at Hclosed) |exact Hat]); subst other.
      exact (closed_spawns Hclosed target Hin).
Qed.
Lemma post_closed tf st owner : owner_post_solution tf st owner ->
  exists result, closed_observation (tf owner) st result /\ D.leq (Sem.observed_direct result) (R.sigma_value st owner) = true.
Proof.
  intros [[direct [reads [effects Hreplay]]] [Hvalues Hspawns]].
  destruct (replay_observation Hreplay) as [result [Hat [Hd [Hr He]]]]; exists result; split.
  - constructor; [exact Hat | |exact (Hspawns result Hat)].
    intros target value Hin; exists value; eapply Sem.rhs_eval_reads_lookup; [exact Hreplay |now rewrite <- Hr].
  - rewrite Hd; exact (proj1 (Hvalues _ _ _ Hreplay)).
Qed.
Lemma below_owner_absent st owner : queue_below st owner -> ~ In owner (R.queue st).
Proof.
  unfold queue_below; rewrite Forall_forall; intros H Hin; specialize (H owner Hin);
    unfold R.rank_lt in H; rewrite lt_irrefl in H; discriminate.
Qed.
Theorem ordinary_commit_observed tf roots st fr direct k : no_side_effects tf ->
  reachable tf roots (configuration st (R.RunCommit fr direct k)) ->
  exists result, closed_observation (tf (R.frame_owner fr)) st result /\ Sem.observed_direct result = direct.
Proof.
  intros Hpure Hreachable.
  pose proof (@reachable_semantic_invariant tf roots _ Hreachable) as Hsem.
  destruct (invariant_observing Hsem) as [[Hcursor Hstack]].
  destruct Hcursor as [reads sides spawns Hprefix Hwatches Hraw Hledger Hspawns].
  set (result := {| Sem.Observation.observed_direct := direct; Sem.Observation.observed_reads := reads;
    Sem.Observation.observed_sides := sides; Sem.Observation.observed_spawns := spawns |}).
  assert (Hquiet : ~ In (R.frame_owner fr) (R.queue st)) by (apply below_owner_absent; eapply ordinary_commit_queue_below; eauto).
  exists result; split; [constructor |reflexivity].
  - split; [apply prefix_return; exact Hprefix |].
    intros target value Hin; symmetry; apply read_value; exact (proj1 (Hwatches Hquiet target value Hin)).
  - intros target value Hin; exists value; exact (proj1 (Hwatches Hquiet target value Hin)).
  - intros target Hin; exact (@live_reference_solved (configuration st (R.RunCommit fr direct k))
    (invariant_frames Hsem) eq_refl target (Hspawns target Hin)).
Qed.
Theorem ordinary_commit_higher_post tf roots st fr direct k : no_side_effects tf ->
  reachable tf roots (configuration st (R.RunCommit fr direct k)) -> forall owner,
  solved st owner -> R.rank_lt st (R.frame_owner fr) owner = true -> owner_post_solution tf st owner.
Proof.
  intros Hpure Hreachable owner Hsolved Hhigher.
  pose proof (@reachable_semantic_invariant tf roots _ Hreachable) as Hsem.
  assert (Hquiet : ~ In owner (R.queue st)).
  { intro Hin; pose proof (@ordinary_commit_queue_below tf roots st fr direct k Hpure Hreachable) as Hbelow.
    unfold queue_below in Hbelow; rewrite Forall_forall in Hbelow; specialize (Hbelow owner Hin).
    pose proof (@lt_trans (R.ranking st) owner (R.frame_owner fr) owner Hbelow Hhigher) as Hcycle;
      rewrite lt_irrefl in Hcycle; discriminate. }
  assert (Hidle : idle (configuration st (R.RunCommit fr direct k)) owner).
  { split; [exact Hquiet |intro Hin].
    pose proof (@reachable_active_ordered tf roots _ Hreachable) as Horder.
    exact (@ordered_head_not_lower (R.ranking st) (R.frame_owner fr) (suspended_owners k) owner Horder Hin Hhigher). }
  destruct (invariant_settled Hsem Hsolved Hidle) as [Hdone].
  apply completed_is_post_solution with (done := Hdone); intros target raw Hin.
  assert (Hempty : Sem.observed_sides (completed_result Hdone) = []) by (exact (Hpure owner _ (completed_trace Hdone))).
  rewrite Hempty in Hin; contradiction.
Qed.

(** Monotonicity transfers a closed observation to a lower store. Dependency
    monotonicity supplies read coverage; effect monotonicity supplies spawn
    coverage and the direct-value bound. *)
Lemma observations_descend body lower upper lower_values upper_values :
  Sem.rhs_dependencies_monotone body -> Sem.rhs_effects_monotone body ->
  (forall x, D.leq (lower_values x) (upper_values x) = true) ->
  Sem.observes_at lower_values body lower -> Sem.observes_at upper_values body upper ->
  Sem.list_included (map fst (Sem.observed_reads lower)) (map fst (Sem.observed_reads upper)) /\ Sem.effects_le lower upper.
Proof.
  intros Hdeps Heffects Hvalues [Hlower Hlow_reads] [Hupper Hupper_reads].
  assert (Hcommon : Sem.common_read_values_le lower upper).
  { intros target low high Hlow Hhigh; rewrite (Hlow_reads target low Hlow), (Hupper_reads target high Hhigh); apply Hvalues. }
  pose proof (Hdeps lower upper Hlower Hupper Hcommon) as Hreads; split; [exact Hreads |].
  apply Heffects; [exact Hlower |exact Hupper |]; intros target value Hin.
  assert (Htarget : In target (map fst (Sem.observed_reads lower))) by (apply in_map_iff; exists (target,value); auto).
  specialize (Hreads target Htarget); apply in_map_iff in Hreads; destruct Hreads as [[x high] [Hx Hhigh]]; cbn in Hx; subst x.
  exists high; split; [exact Hhigh |eapply Hcommon; eauto].
Qed.
Lemma closed_descend body before after upper lower :
  Sem.rhs_dependencies_monotone body -> Sem.rhs_effects_monotone body ->
  preserves_live before after -> (forall x, D.leq (R.sigma_value after x) (R.sigma_value before x) = true) ->
  closed_observation body before upper -> Sem.observes_at (R.sigma_value after) body lower ->
  closed_observation body after lower /\ D.leq (Sem.observed_direct lower) (Sem.observed_direct upper) = true.
Proof.
  intros Hdeps Heffects Hlive Hvalues Hclosed Hlower.
  destruct (@observations_descend body lower upper (R.sigma_value after) (R.sigma_value before)
    Hdeps Heffects Hvalues Hlower (closed_at Hclosed)) as [Hreads Heffect]; split.
  - constructor; [exact Hlower | |].
    + intros target value Hin; apply Hlive.
      assert (Htarget : In target (map fst (Sem.observed_reads lower))) by (apply in_map_iff; exists (target,value); auto).
      specialize (Hreads target Htarget); apply in_map_iff in Hreads; destruct Hreads as [[x high] [Hx Hhigh]]; cbn in Hx; subst x.
      exact (closed_reads Hclosed target high Hhigh).
    + intros target Hin; apply Hlive; apply (closed_spawns Hclosed); eapply Sem.Observation.spawn_effects_le; eauto.
  - exact (Sem.Observation.direct_effect_le Heffect).
Qed.
Lemma ordinary_descending_post tf before after owner upper : monotonic_system tf -> no_side_effects tf ->
  preserves_live before after -> (forall x, D.leq (R.sigma_value after x) (R.sigma_value before x) = true) ->
  closed_observation (tf owner) before upper ->
  D.leq (Sem.observed_direct upper) (R.sigma_value after owner) = true -> owner_post_solution tf after owner.
Proof.
  intros Hmono Hpure Hlive Hvalues Hclosed Hbound.
  destruct (observation_total (R.sigma_value after) (tf owner)) as [lower Hlower].
  destruct (@closed_descend (tf owner) before after upper lower (proj1 (Hmono owner)) (proj2 (Hmono owner))
    Hlive Hvalues Hclosed Hlower) as [Hclosed' Hdirect].
  eapply closed_post; [exact Hpure |exact Hclosed' |eapply DL.leq_trans; eauto].
Qed.
Lemma ordinary_post_preserved_below tf before after owner : monotonic_system tf -> no_side_effects tf ->
  preserves_live before after -> (forall x, D.leq (R.sigma_value after x) (R.sigma_value before x) = true) ->
  R.sigma_value after owner = R.sigma_value before owner -> owner_post_solution tf before owner -> owner_post_solution tf after owner.
Proof.
  intros Hmono Hpure Hlive Hvalues Hsame Hpost; destruct (post_closed Hpost) as [upper [Hclosed Hbound]].
  eapply ordinary_descending_post; [exact Hmono |exact Hpure |exact Hlive |exact Hvalues |exact Hclosed |now rewrite Hsame].
Qed.

Lemma cursor_residual_closed tf live st fr body (current : cursor tf live st fr body) :
  ~ In (R.frame_owner fr) (R.queue st) -> owner_post_solution tf st (R.frame_owner fr) ->
  forall result, Sem.observes_at (R.sigma_value st) body result -> closed_observation body st result.
Proof.
  intros Hquiet Hpost result [Htrace Hvalues].
  destruct (post_closed Hpost) as [upper [Hclosed Hbound]].
  destruct current as [reads sides spawns Hprefix Hwatches Hraw Hledger Hspawns].
  set (whole := {| Sem.Observation.observed_direct := Sem.observed_direct result;
    Sem.Observation.observed_reads := reads ++ Sem.observed_reads result;
    Sem.Observation.observed_sides := sides ++ Sem.observed_sides result;
    Sem.Observation.observed_spawns := spawns ++ Sem.observed_spawns result |}).
  assert (Hat : Sem.observes_at (R.sigma_value st) (tf (R.frame_owner fr)) whole).
  { split; [exact (Hprefix result Htrace) |].
    intros target value Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    - symmetry; apply read_value; exact (proj1 (Hwatches Hquiet target value Hin)).
    - apply Hvalues; exact Hin. }
  assert (Heq : whole = upper) by (eapply observation_unique; [exact Hat |exact (closed_at Hclosed)]).
  constructor; [split; assumption | |].
  - intros target value Hin; apply (closed_reads Hclosed target value); rewrite <- Heq; apply in_or_app; right; exact Hin.
  - intros target Hin; apply (closed_spawns Hclosed target); rewrite <- Heq; apply in_or_app; right; exact Hin.
Qed.
Definition semantic_frontier tf st owner := forall target,
  target = owner \/ R.rank_lt st owner target = true -> solved st target /\ owner_post_solution tf st target.
Lemma ordinary_commit_frontier tf roots st fr direct k : no_side_effects tf ->
  reachable tf roots (configuration st (R.RunCommit fr direct k)) ->
  D.leq direct (R.sigma_value st (R.frame_owner fr)) = true -> semantic_frontier tf st (R.frame_owner fr).
Proof.
  intros Hpure Hreachable Hdescending target [->|Hhigher].
  - split.
    + pose proof (@reachable_frames_live tf roots _ Hreachable) as Hframes; inversion Hframes; assumption.
    + destruct (@ordinary_commit_observed tf roots st fr direct k Hpure Hreachable) as [result [Hclosed Hd]].
      eapply closed_post; [exact Hpure |exact Hclosed |now rewrite Hd].
  - assert (Hlive : solved st target).
    { pose proof (@ordinary_discovery_ready tf roots _ Hpure Hreachable) as Hready.
      apply Hready; destruct (@lt_ranks (R.ranking st) (R.frame_owner fr) target Hhigher) as [rx [ry [_ [Hy _]]]]; exists ry; exact Hy. }
    split; [exact Hlive |eapply ordinary_commit_higher_post; eauto].
Qed.
Lemma commit_value_other st fr direct next next_fr target : R.set_value st fr direct = (next,next_fr) ->
  target <> R.frame_owner fr -> R.sigma_value next target = R.sigma_value st target.
Proof.
  intros Hset Hneq; unfold R.sigma_value; rewrite (commit_other (@commit_footprint st fr direct next next_fr Hset) Hneq); reflexivity.
Qed.
Lemma commit_descending st fr direct next next_fr :
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
  D.leq (snd (U.update false (R.frame_owner fr) (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
    (D.join direct (R.aggregate st (R.frame_owner fr))))) (R.sigma_value st (R.frame_owner fr)) = true ->
  R.set_value st fr direct = (next,next_fr) -> forall target,
  D.leq (R.sigma_value next target) (R.sigma_value st target) = true.
Proof.
  intros Hinput Hupdate Hset target; destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq].
  - unfold R.set_value in Hset; split_program Hset; try apply DL.leq_refl.
    all: unfold R.sigma_value; cbn [R.enqueue_all R.with_readers R.with_queue R.with_sigma R.sigma]; rewrite ML.lookup_update_same.
    all: try exact Hinput.
    all: exact Hupdate.
  - rewrite (@commit_value_other st fr direct next next_fr target Hset Hneq); apply DL.leq_refl.
Qed.
Lemma frontier_descending_commit tf roots st fr direct k next next_fr parent : monotonic_system tf -> no_side_effects tf ->
  reachable tf roots (configuration st (R.RunCommit fr direct k)) ->
  semantic_frontier tf st parent ->
  (forall target, D.leq (R.sigma_value next target) (R.sigma_value st target) = true) ->
  R.set_value st fr direct = (next,next_fr) -> semantic_frontier tf next parent.
Proof.
  intros Hmono Hpure Hreachable Hfront Hdescending Hset target Htarget.
  pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview.
  assert (Hbefore : target = parent \/ R.rank_lt st parent target = true).
  { unfold R.rank_lt in Htarget; rewrite (commit_ranking Hview) in Htarget; exact Htarget. }
  destruct (Hfront target Hbefore) as [Hlive Hpost]; split; [apply (preserves_live_commit Hset); exact Hlive |].
  destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq].
  - destruct (@ordinary_commit_observed tf roots st fr direct k Hpure Hreachable) as [upper [Hclosed Hd]].
    eapply ordinary_descending_post; [exact Hmono |exact Hpure |exact (@preserves_live_commit st fr direct next next_fr Hset) |exact Hdescending |exact Hclosed |].
    rewrite Hd; eapply DL.leq_trans; [apply DL.join_upper_left |eapply commit_sound; exact Hset].
  - eapply ordinary_post_preserved_below; [exact Hmono |exact Hpure |exact (@preserves_live_commit st fr direct next next_fr Hset) |
      exact Hdescending |eapply commit_value_other; eauto |exact Hpost].
Qed.
Lemma ordinary_new_narrowing_frontier tf roots st fr direct k next next_fr : monotonic_system tf -> no_side_effects tf ->
  reachable tf roots (configuration st (R.RunCommit fr direct k)) ->
  (forall target, D.leq (R.sigma_value next target) (R.sigma_value st target) = true) ->
  R.set_value st fr direct = (next,next_fr) -> semantic_frontier tf next (R.frame_owner fr).
Proof.
  intros Hmono Hpure Hreachable Hdescending Hset.
  assert (Hdirect : D.leq direct (R.sigma_value st (R.frame_owner fr)) = true).
  { eapply DL.leq_trans; [eapply DL.leq_trans; [apply DL.join_upper_left |eapply commit_sound; exact Hset] |apply Hdescending]. }
  eapply frontier_descending_commit; [exact Hmono |exact Hpure |exact Hreachable |
    eapply ordinary_commit_frontier; eauto |exact Hdescending |exact Hset].
Qed.

Definition outside_commit ctrl := match ctrl with R.RunCommit _ _ _ => False | _ => True end.
Lemma noncommit_phase_origin tf before after owner phase : NoDup (active_owners (R.cfg_control before)) -> outside_commit (R.cfg_control before) ->
  step tf before after -> owner_phase (R.cfg_control after) owner = Some phase ->
  phase = U.initial_phase false owner \/ owner_phase (R.cfg_control before) owner = Some phase.
Proof.
  intros Hunique Hnot Hstep Hphase; destruct before as [st ctrl]; cbn [R.cfg_control] in Hunique, Hnot |- *.
  unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [outside_commit] in Hnot; cbn [active_owners] in Hunique; try contradiction;
    unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep; split_program Hstep.
  all: repeat match goal with Hget : R.complete_get _ _ _ = (_,_,_) |- _ =>
    let Ho := fresh "get_owner" in let Hp := fresh "get_phase" in
    pose proof (get_owner Hget) as Ho; pose proof (get_phase Hget) as Hp; clear Hget end.
  all: cbn [R.cfg_control owner_phase stack_phase R.frame_owner R.frame_phase R.with_frame_side R.fresh_frame] in Hphase |- *;
    repeat match goal with Ho : R.frame_owner _ = _ |- _ => rewrite Ho in Hphase; clear Ho end;
    repeat match goal with Hp : R.frame_phase _ = _ |- _ => rewrite Hp in Hphase; clear Hp end.
  all: repeat match goal with H : context [if V.eq_dec ?x ?y then _ else _] |- _ =>
    destruct (V.eq_dec x y); [subst |]; cbn in Hphase |- * end.
  all: try solve [right; exact Hphase].
  all: try solve [discriminate].
  all: try solve [injection Hphase as Hphase; left; symmetry; exact Hphase].
  all: match goal with |- _ \/ (if V.eq_dec ?owner ?current then _ else _) = _ =>
    destruct (V.eq_dec owner current) as [Heq|Hneq]; [subst owner |right; exact Hphase] end.
  all: inversion Hunique; subst; exfalso; apply H1; eapply stack_phase_present; exact Hphase.
Qed.
Lemma observe_known_identity st target : ranked (R.ranking st) target -> R.observe st target = st.
Proof.
  intros [rank Hrank]; unfold R.observe; rewrite (@RL.observe_existing _ _ _ Hrank);
    destruct st; reflexivity.
Qed.
Lemma solved_known st target : store_wf (fun _ => True) st -> solved st target -> ranked (R.ranking st) target.
Proof. intros Hstore [value Hlookup]; exact (proj2 (proj1 (refs_sigma (store_references Hstore) Hlookup))). Qed.
Lemma closed_get_target st target tail result : closed_observation (Syntax.Get target tail) st result -> solved st target.
Proof. intros [[Htrace _] Hreads _]; inversion Htrace; subst result; eapply Hreads; left; reflexivity. Qed.
Lemma closed_spawn_target st target tail result : closed_observation (Syntax.Spawn target tail) st result -> solved st target.
Proof. intros [[Htrace _] _ Hspawns]; inversion Htrace; subst result; apply Hspawns; left; reflexivity. Qed.

Record ordinary_phase_laws := {
  phase_safe : U.phase -> Prop;
  phase_narrowing : U.phase -> Prop;
  initial_phase_safe : forall owner, phase_safe (U.initial_phase false owner);
  initial_phase_not_narrowing : forall owner, ~ phase_narrowing (U.initial_phase false owner);
  ordinary_update_safe : forall owner phase old input, phase_safe phase ->
    (phase_narrowing phase -> D.leq input old = true) -> phase_safe (fst (U.update false owner phase old input));
  ordinary_update_narrowing : forall owner phase old input, phase_safe phase ->
    phase_narrowing (fst (U.update false owner phase old input)) -> D.leq input old = true;
  ordinary_update_descends : forall owner phase old input, phase_safe phase -> D.leq input old = true ->
    D.leq (snd (U.update false owner phase old input)) old = true
}.
Section OrdinaryPhases.
Variable phases : ordinary_phase_laws.
Definition phase_frontiers tf c := forall owner phase, owner_phase (R.cfg_control c) owner = Some phase ->
  phase_safe phases phase /\ (phase_narrowing phases phase -> semantic_frontier tf (R.cfg_state c) owner).
Definition some_narrowing c := exists owner phase, owner_phase (R.cfg_control c) owner = Some phase /\ phase_narrowing phases phase.
Lemma narrowing_current_post tf roots st fr body k : reachable tf roots (configuration st (R.RunRhs fr body k)) ->
  phase_frontiers tf (configuration st (R.RunRhs fr body k)) -> some_narrowing (configuration st (R.RunRhs fr body k)) ->
  owner_post_solution tf st (R.frame_owner fr).
Proof.
  intros Hreachable Hfront [owner [phase [Hphase Hnarrow]]].
  destruct (Hfront owner phase Hphase) as [_ Hfrontier]; specialize (Hfrontier Hnarrow).
  assert (Habove : R.frame_owner fr = owner \/ R.rank_lt st owner (R.frame_owner fr) = true).
  { destruct (V.eq_dec (R.frame_owner fr) owner) as [Heq|Hneq]; [left; exact Heq |right].
    pose proof (@reachable_active_ordered tf roots _ Hreachable) as Hordered.
    pose proof (@owner_phase_present (R.RunRhs fr body k) owner phase Hphase) as Hin.
    exact (@ordered_member_lower st (R.frame_owner fr) (suspended_owners k) owner Hordered Hin ltac:(congruence)). }
  exact (proj2 (Hfrontier (R.frame_owner fr) Habove)).
Qed.
Lemma narrowing_get_materialized tf roots st fr target tail k : no_side_effects tf ->
  reachable tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  phase_frontiers tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  some_narrowing (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) -> solved st target.
Proof.
  intros Hpure Hreachable Hfront Hnarrow.
  pose proof (@reachable_semantic_invariant tf roots _ Hreachable) as Hsem.
  destruct (invariant_observing Hsem) as [[Hcursor Hstack]].
  destruct (observation_total (R.sigma_value st) (Syntax.Get target tail)) as [result Hat].
  eapply closed_get_target; eapply cursor_residual_closed.
  - exact Hcursor.
  - apply below_owner_absent; eapply ordinary_evaluation_queue_below; eauto.
  - eapply narrowing_current_post; eauto.
  - exact Hat.
Qed.
Lemma narrowing_spawn_materialized tf roots st fr target tail k : no_side_effects tf ->
  reachable tf roots (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  phase_frontiers tf (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  some_narrowing (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) -> solved st target.
Proof.
  intros Hpure Hreachable Hfront Hnarrow.
  pose proof (@reachable_semantic_invariant tf roots _ Hreachable) as Hsem.
  destruct (invariant_observing Hsem) as [[Hcursor Hstack]].
  destruct (observation_total (R.sigma_value st) (Syntax.Spawn target tail)) as [result Hat].
  eapply closed_spawn_target; eapply cursor_residual_closed.
  - exact Hcursor.
  - apply below_owner_absent; eapply ordinary_evaluation_queue_below; eauto.
  - eapply narrowing_current_post; eauto.
  - exact Hat.
Qed.

Lemma ordinary_noncommit_values tf before after : ordinary_config before -> outside_commit (R.cfg_control before) ->
  step tf before after -> forall target, R.sigma_value (R.cfg_state after) target = R.sigma_value (R.cfg_state before) target.
Proof.
  intros [_ Hordinary] Hnot Hstep target; destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in *.
  unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [outside_commit ordinary_control] in Hnot, Hordinary; try contradiction.
  all: try match goal with H : _ /\ pure_rhs ?body /\ _ |- _ =>
    destruct body; [| |exfalso; eapply pure_no_side; exact (proj1 (proj2 H)) |] end.
  all: try match goal with H : _ /\ ?pending = [] /\ _ |- _ => destruct H as [_ [-> _]] end.
  all: split_program Hstep; cbn [R.cfg_state].
  all: try match goal with Hget : R.complete_get _ _ _ = (_,_,_) |- _ => rewrite (get_sigma_value target Hget) end.
  all: repeat rewrite materialize_sigma_value.
  all: unfold R.sigma_value; cbn [R.with_queue R.enqueue R.sigma R.publish_targets]; try rewrite observe_sigma; try reflexivity.
  all: try solve [match goal with |- context [if R.is_materialized ?base ?x then _ else _] => destruct (R.is_materialized base x) end;
    cbn [R.enqueue R.with_queue R.sigma]; rewrite observe_sigma; reflexivity].
  all: unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity.
Qed.
Lemma narrowing_noncommit_rank tf roots before after : no_side_effects tf -> reachable tf roots before ->
  phase_frontiers tf before -> some_narrowing before -> outside_commit (R.cfg_control before) -> step tf before after ->
  R.ranking (R.cfg_state after) = R.ranking (R.cfg_state before).
Proof.
  intros Hpure Hreachable Hfront Hnarrow Hnot Hstep.
  pose proof (@reachable_rank_configuration tf roots before Hreachable) as [Hstore Hrefs].
  pose proof (@ordinary_reachable tf roots before Hpure Hreachable) as [_ Hordinary].
  destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in *.
  pose proof Hstep as Hnext; unfold step, R.next_config in Hnext; cbn [R.cfg_state R.cfg_control] in Hnext.
  destruct ctrl; cbn [outside_commit ordinary_control] in Hnot, Hordinary; try contradiction.
  all: try solve [destruct Hnarrow as [owner [phase [Hphase _]]]; discriminate Hphase].
  - inversion Hnext; subst after; cbn [R.cfg_state]; apply materialize_rank.
  - destruct Hordinary as [_ [Hcode _]]; destruct r as [direct|target tail|target raw tail|target tail].
    + inversion Hnext; reflexivity.
    + assert (Hknown : R.observe st target = st).
      { apply observe_known_identity, (solved_known Hstore).
        eapply narrowing_get_materialized; eauto. }
      rewrite Hknown in Hnext; split_program Hnext; cbn [R.cfg_state]; try reflexivity.
      match goal with Hget : R.complete_get _ _ _ = (_,_,_) |- _ =>
        pose proof (get_rank Hget) as Hrank; destruct (R.is_materialized st target); exact Hrank end.
    + exfalso; exact (pure_no_side Hcode).
    + assert (Hknown : R.observe st target = st).
      { apply observe_known_identity, (solved_known Hstore).
        eapply narrowing_spawn_materialized; eauto. }
      rewrite Hknown in Hnext; split_program Hnext; cbn [R.cfg_state]; try reflexivity; rewrite materialize_rank; reflexivity.
  - destruct Hordinary as [_ [-> _]]; inversion Hnext; reflexivity.
  - split_program Hnext; cbn [R.cfg_state]; try reflexivity; apply close_rank.
  - destruct c; split_program Hnext; cbn [R.cfg_state]; try reflexivity; eapply get_rank; eassumption.
Qed.
Lemma frontier_static tf before after parent : monotonic_system tf -> no_side_effects tf -> preserves_live before after ->
  R.ranking after = R.ranking before -> (forall target, R.sigma_value after target = R.sigma_value before target) ->
  semantic_frontier tf before parent -> semantic_frontier tf after parent.
Proof.
  intros Hmono Hpure Hlive Hr Hv Hfront target Htarget; unfold R.rank_lt in Htarget; rewrite Hr in Htarget.
  destruct (Hfront target Htarget) as [Hsolved Hpost]; split; [apply Hlive; exact Hsolved |].
  eapply ordinary_post_preserved_below; [exact Hmono |exact Hpure |exact Hlive | |apply Hv |exact Hpost].
  intro x; rewrite Hv; apply DL.leq_refl.
Qed.
Lemma phase_frontier_noncommit tf roots before after : monotonic_system tf -> no_side_effects tf -> reachable tf roots before ->
  phase_frontiers tf before -> outside_commit (R.cfg_control before) -> step tf before after -> phase_frontiers tf after.
Proof.
  intros Hmono Hpure Hreachable Hfront Hnot Hstep owner phase Hphase.
  destruct (@noncommit_phase_origin tf before after owner phase
    (@reachable_owners_unique tf roots before Hreachable) Hnot Hstep Hphase) as [Hinitial|Hold].
  - subst phase; split; [apply initial_phase_safe |intro Hnarrow; exfalso; exact (initial_phase_not_narrowing phases owner Hnarrow)].
  - destruct (Hfront owner phase Hold) as [Hsafe Hpost]; split; [exact Hsafe |intro Hnarrow].
    eapply frontier_static; [exact Hmono |exact Hpure |eapply next_preserves_live; exact Hstep | | |apply Hpost; exact Hnarrow].
    + eapply narrowing_noncommit_rank; [exact Hpure |exact Hreachable |exact Hfront |exists owner, phase; auto |exact Hnot |exact Hstep].
    + eapply ordinary_noncommit_values; [eapply ordinary_reachable; eauto |exact Hnot |exact Hstep].
Qed.
Lemma commit_input_below tf roots st fr direct k : no_side_effects tf ->
  reachable tf roots (configuration st (R.RunCommit fr direct k)) -> owner_post_solution tf st (R.frame_owner fr) ->
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true.
Proof.
  intros Hpure Hreachable Hpost; destruct (@ordinary_commit_observed tf roots st fr direct k Hpure Hreachable) as [result [Hclosed Hd]].
  pose proof (@ordinary_aggregate tf roots _ (R.frame_owner fr) Hpure Hreachable) as Haggregate.
  change (R.aggregate st (R.frame_owner fr) = D.bottom) in Haggregate; rewrite Haggregate; apply DL.join_least; [|apply DL.bottom_least].
  rewrite <- Hd; exact (proj1 (owner_post_observation Hpost (closed_at Hclosed))).
Qed.
Lemma safe_commit_phase st fr direct next next_fr : phase_safe phases (R.frame_phase fr) ->
  (phase_narrowing phases (R.frame_phase fr) ->
    D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true) ->
  R.set_value st fr direct = (next,next_fr) -> phase_safe phases (R.frame_phase next_fr) /\
  (phase_narrowing phases (R.frame_phase next_fr) ->
    D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true).
Proof.
  intros Hsafe Hinput Hset; unfold R.set_value in Hset; split_program Hset;
    cbn [R.frame_phase R.with_frame_phase]; try solve [split; assumption].
  all: split; [eapply ordinary_update_safe; eauto |intro Hnarrow; eapply ordinary_update_narrowing; eauto].
Qed.
Lemma frontier_queue tf st parent queue : semantic_frontier tf st parent -> semantic_frontier tf (R.with_queue st queue) parent.
Proof. intros H target Htarget; apply H; exact Htarget. Qed.

Lemma phase_frontier_commit tf roots st fr direct k next next_fr : monotonic_system tf -> no_side_effects tf ->
  reachable tf roots (configuration st (R.RunCommit fr direct k)) ->
  phase_frontiers tf (configuration st (R.RunCommit fr direct k)) -> R.set_value st fr direct = (next,next_fr) ->
  phase_frontiers tf (configuration (R.requeue_changed_controlled_owner st next (R.frame_owner fr)) (R.RunDrain next_fr k)).
Proof.
  intros Hmono Hpure Hreachable Hfront Hset.
  destruct (Hfront (R.frame_owner fr) (R.frame_phase fr) (@phase_commit fr direct k)) as [Hsafe Hown_front].
  assert (Hinput : phase_narrowing phases (R.frame_phase fr) ->
    D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true).
  { intro Hnarrow; eapply commit_input_below; [exact Hpure |exact Hreachable |].
    exact (proj2 (Hown_front Hnarrow (R.frame_owner fr) (or_introl eq_refl))). }
  destruct (@safe_commit_phase st fr direct next next_fr Hsafe Hinput Hset) as [Hnext_safe Hnext_input].
  pose proof (@commit_footprint st fr direct next next_fr Hset) as Hview.
  intros owner phase Hphase; cbn [configuration R.cfg_control owner_phase] in Hphase; rewrite (commit_owner Hview) in Hphase.
  destruct (V.eq_dec owner (R.frame_owner fr)) as [Heq|Hneq].
  - subst owner; injection Hphase as Hphase; subst phase; split; [exact Hnext_safe |intro Hnarrow].
    assert (Hdescending : forall target, D.leq (R.sigma_value next target) (R.sigma_value st target) = true).
    { eapply commit_descending; [apply Hnext_input; exact Hnarrow | |exact Hset].
      eapply ordinary_update_descends; [exact Hsafe |apply Hnext_input; exact Hnarrow]. }
    apply frontier_queue; eapply ordinary_new_narrowing_frontier; eauto.
  - assert (Hold : owner_phase (R.RunCommit fr direct k) owner = Some phase).
    { cbn [owner_phase]; destruct (V.eq_dec owner (R.frame_owner fr)); [contradiction |exact Hphase]. }
    destruct (Hfront owner phase Hold) as [Howner_safe Howner_front]; split; [exact Howner_safe |intro Hnarrow].
    specialize (Howner_front Hnarrow).
    assert (Hhigher : R.rank_lt st owner (R.frame_owner fr) = true).
    { pose proof (@reachable_active_ordered tf roots _ Hreachable) as Horder.
      pose proof (@owner_phase_present (R.RunCommit fr direct k) owner phase Hold) as Hin.
      exact (@ordered_member_lower st (R.frame_owner fr) (suspended_owners k) owner Horder Hin Hneq). }
    assert (Hbelow : D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true).
    { eapply commit_input_below; [exact Hpure |exact Hreachable |exact (proj2 (Howner_front (R.frame_owner fr) (or_intror Hhigher)))]. }
    assert (Hdescending : forall target, D.leq (R.sigma_value next target) (R.sigma_value st target) = true).
    { eapply commit_descending; [exact Hbelow | |exact Hset].
      eapply ordinary_update_descends; [exact Hsafe |exact Hbelow]. }
    apply frontier_queue; eapply frontier_descending_commit; [exact Hmono |exact Hpure |exact Hreachable |
      exact Howner_front |exact Hdescending |exact Hset].
Qed.
Theorem next_phase_frontiers tf roots before after : monotonic_system tf -> no_side_effects tf -> reachable tf roots before ->
  phase_frontiers tf before -> step tf before after -> phase_frontiers tf after.
Proof.
  intros Hmono Hpure Hreachable Hfront Hstep; destruct before as [st ctrl]; destruct ctrl.
  all: try solve [eapply phase_frontier_noncommit; [exact Hmono |exact Hpure |exact Hreachable |exact Hfront |exact I |exact Hstep]].
  unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct (R.set_value st f t) as [next next_fr] eqn:Hset; inversion Hstep; subst after;
    eapply phase_frontier_commit; eauto.
Qed.
Theorem ordinary_phase_frontiers tf roots c : monotonic_system tf -> no_side_effects tf -> reachable tf roots c -> phase_frontiers tf c.
Proof.
  intros Hmono Hpure Hpath.
  assert (Hinitial : phase_frontiers tf (R.initial_config roots)) by (intros owner phase Hphase; discriminate Hphase).
  assert (Hpreserve : forall a b, steps tf a b -> reachable tf roots a -> phase_frontiers tf a -> phase_frontiers tf b).
  { intros a b Hsteps; induction Hsteps; intros Hreachable Hfirst; auto.
    apply IHHsteps; [eapply reachable_advance; eauto |eapply next_phase_frontiers; eauto]. }
  exact (Hpreserve _ _ Hpath (@steps_refl tf (R.initial_config roots)) Hinitial).
Qed.
Fixpoint continuation_avoids_fallback k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => True
  | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest
  | R.KDead fr _ _ rest | R.KDrain fr rest => phase_safe phases (R.frame_phase fr) /\ continuation_avoids_fallback rest
  end.
Definition control_avoids_fallback ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
  | R.StartEpisode _ k | R.Return k => continuation_avoids_fallback k
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k =>
      phase_safe phases (R.frame_phase fr) /\ continuation_avoids_fallback k
  end.
Lemma stack_phases_safe k : NoDup (suspended_owners k) ->
  (forall owner phase, stack_phase k owner = Some phase -> phase_safe phases phase) -> continuation_avoids_fallback k.
Proof.
  induction k; cbn [suspended_owners continuation_avoids_fallback]; intros Hunique Hsafe; try exact I.
  all: inversion Hunique; subst; split.
  all: try solve [apply (Hsafe (R.frame_owner f) (R.frame_phase f)); cbn [stack_phase]; destruct (V.eq_dec (R.frame_owner f) (R.frame_owner f)); [reflexivity |contradiction]].
  all: apply IHk; [assumption |]; intros owner phase Hphase.
  all: assert (Hneq : owner <> R.frame_owner f) by (intro Heq; subst owner; apply H1; eapply stack_phase_present; exact Hphase).
  all: apply (Hsafe owner phase); cbn [stack_phase]; destruct (V.eq_dec owner (R.frame_owner f)); [contradiction |exact Hphase].
Qed.
Lemma control_phases_safe ctrl : NoDup (active_owners ctrl) ->
  (forall owner phase, owner_phase ctrl owner = Some phase -> phase_safe phases phase) -> control_avoids_fallback ctrl.
Proof.
  destruct ctrl; cbn [active_owners control_avoids_fallback]; intros Hunique Hsafe; try exact I.
  - inversion Hunique; subst; eapply stack_phases_safe; eauto.
  - exact (@stack_phases_safe (R.KDrain f c) Hunique Hsafe).
  - exact (@stack_phases_safe (R.KDrain f c) Hunique Hsafe).
  - exact (@stack_phases_safe (R.KDrain f c) Hunique Hsafe).
  - exact (@stack_phases_safe (R.KDrain f c) Hunique Hsafe).
  - eapply stack_phases_safe; eauto.
Qed.
Definition avoids_fallback tf roots := forall c, reachable tf roots c -> control_avoids_fallback (R.cfg_control c).
Theorem ordinary_avoids_fallback tf roots : monotonic_system tf -> no_side_effects tf -> avoids_fallback tf roots.
Proof.
  intros Hmono Hpure c Hreachable; apply control_phases_safe; [eapply reachable_owners_unique; exact Hreachable |].
  intros owner phase Hphase; exact (proj1 (@ordinary_phase_frontiers tf roots c Hmono Hpure Hreachable owner phase Hphase)).
Qed.

Lemma drained_framed ctrl : forall owner, In owner (drained_owners ctrl) -> In owner (framed_owners ctrl).
Proof.
  assert (Hstack : forall k owner, In owner (drained_stack k) -> In owner (suspended_owners k)).
  { intros k owner Hin; exact (@drained_parent k owner Hin). }
  destruct ctrl; cbn [drained_owners framed_owners]; cbn [active_owners]; intros owner Hin; cbn in Hin |- *; try contradiction; intuition eauto.
Qed.
Lemma ready_solved_before tf before after owner : frames_live before -> waiting_control before ->
  ~ committing before owner -> step tf before after -> incoming_ready after owner ->
  solved (R.cfg_state after) owner -> solved (R.cfg_state before) owner.
Proof.
  intros Hframes Hwaiting Hnot Hstep [Hquiet [Hidle|Hdrained]] Hsolved.
  - destruct (@next_solved_origin tf before after Hframes Hwaiting Hstep owner Hsolved) as [Hold|[Hq|Ha]]; auto; contradiction.
  - destruct (@next_drained_origin tf before after Hstep owner Hdrained) as [Hold|Hcommit]; [|contradiction].
    unfold frames_live in Hframes; rewrite Forall_forall in Hframes; apply Hframes; apply drained_framed; exact Hold.
Qed.
Lemma ordinary_ready_snapshot tf roots before after owner : no_side_effects tf -> reachable tf roots before ->
  ~ In owner (R.queue (R.cfg_state before)) -> ~ committing before owner -> step tf before after ->
  frame_snapshot (R.cfg_state before) (R.cfg_state after) [owner].
Proof.
  intros Hpure Hreachable Hquiet Hnot Hstep.
  pose proof (@ordinary_reachable tf roots before Hpure Hreachable) as [_ Hordinary].
  destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in *.
  unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct ctrl; cbn [ordinary_control] in Hordinary.
  all: try match goal with H : _ /\ pure_rhs ?body /\ _ |- _ =>
    destruct body; [| |exfalso; eapply pure_no_side; exact (proj1 (proj2 H)) |] end.
  all: try match goal with H : _ /\ ?pending = [] /\ _ |- _ => destruct H as [_ [-> _]] end.
  all: split_program Hstep; cbn [R.cfg_state].
  all: try solve [apply snapshot_identity |apply snapshot_observe |apply snapshot_publish |apply snapshot_close |apply snapshot_materialize].
  all: try solve [apply snapshot_static; try reflexivity; intros x [<-|Hfalse] Hin; [exfalso; apply Hquiet; exact Hin |contradiction]].
  all: try match goal with Hget : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- _ =>
    eapply snapshot_compose; [|exact (snapshot_get [owner] Hget)];
      try solve [apply snapshot_identity |apply snapshot_observe];
      destruct (R.is_materialized (R.observe st target) target); [apply snapshot_observe |];
      eapply snapshot_compose; [apply snapshot_observe |apply snapshot_enqueue] end.
  all: try solve [match goal with Hget : R.complete_get _ _ _ = (_,_,_) |- _ => exact (snapshot_get [owner] Hget) end].
  all: try solve [eapply snapshot_compose; [apply snapshot_observe |]; eapply snapshot_compose; [apply snapshot_enqueue |apply snapshot_materialize]].
  all: match goal with Hset : R.set_value ?base ?fr ?direct = (?next,?next_fr) |- _ =>
    eapply snapshot_compose; [eapply snapshot_commit; [exact Hset |] |apply snapshot_requeue];
    intros x [<-|Hfalse] Heq; [apply Hnot; exists fr, direct, c; split; [reflexivity |exact Heq] |contradiction] end.
Qed.

Section OrdinaryFixedness.
Variable narrow : D.t -> D.t -> D.t.
Variable narrow_lower : forall old input, D.leq input old = true -> D.leq input (narrow old input) = true.
Variable narrow_upper : forall old input, D.leq input old = true -> D.leq (narrow old input) old = true.
Variable update_narrow : forall owner phase old input, phase_safe phases phase -> D.leq input old = true ->
  snd (U.update false owner phase old input) = narrow old input.

Lemma narrow_equiv (owner : V.t) phase old old' input input' : phase_safe phases phase ->
  D.leq input old = true -> D.leq input' old' = true -> eqv old old' -> eqv input input' ->
  eqv (narrow old input) (narrow old' input').
Proof.
  intros Hsafe Hbelow Hbelow' Hold Hinput.
  rewrite <- (@update_narrow owner phase old input Hsafe Hbelow), <- (@update_narrow owner phase old' input' Hsafe Hbelow').
  exact (@UL.update_extensional false owner phase old old' input input' Hold Hinput).
Qed.
Lemma uncontrolled_commit_value st fr direct next next_fr : S.mem (R.frame_owner fr) (R.controlled st) = false ->
  R.set_value st fr direct = (next,next_fr) -> eqv (R.sigma_value next (R.frame_owner fr)) (D.join direct (R.aggregate st (R.frame_owner fr))).
Proof.
  intros Hcontrolled Hset; unfold R.set_value in Hset; rewrite Hcontrolled in Hset; split_program Hset.
  all: try solve [apply eqv_sym, eqv_bool; assumption].
  all: unfold R.sigma_value; cbn [R.enqueue_all R.with_readers R.with_queue R.with_sigma R.sigma]; rewrite ML.lookup_update_same; apply eqv_refl.
Qed.
Lemma ordinary_quiet_commit_fixed tf roots st fr direct k next next_fr : Features.recompute_controlled = true ->
  no_side_effects tf -> reachable tf roots (configuration st (R.RunCommit fr direct k)) -> phase_safe phases (R.frame_phase fr) ->
  R.set_value st fr direct = (next,next_fr) ->
  ~ In (R.frame_owner fr) (R.queue (R.requeue_changed_controlled_owner st next (R.frame_owner fr))) ->
  eqv (narrow (R.sigma_value next (R.frame_owner fr)) direct) (R.sigma_value next (R.frame_owner fr)).
Proof.
  intros Hon Hpure Hreachable Hsafe Hset Hquiet.
  set (input := D.join direct (R.aggregate st (R.frame_owner fr))).
  assert (Hinput : eqv input direct).
  { unfold input; pose proof (@ordinary_aggregate tf roots _ (R.frame_owner fr) Hpure Hreachable) as Haggregate.
    change (R.aggregate st (R.frame_owner fr) = D.bottom) in Haggregate; rewrite Haggregate.
    split; [apply DL.join_least; [apply DL.leq_refl |apply DL.bottom_least] |apply DL.join_upper_left]. }
  destruct (S.mem (R.frame_owner fr) (R.controlled st)) eqn:Hcontrolled.
  - pose proof (@quiet_controlled_commit st next (R.frame_owner fr) Hon Hcontrolled Hquiet) as Hsame.
    pose proof (@quiet_commit_narrowing_fixed narrow (phase_safe phases) update_narrow narrow_lower narrow_upper
      st fr direct next next_fr Hon Hsafe Hcontrolled Hset Hquiet) as Hfixed.
    assert (Hbelow : D.leq input (R.sigma_value st (R.frame_owner fr)) = true).
    { eapply DL.leq_trans; [exact (@commit_sound st fr direct next next_fr Hset) |exact (proj1 Hsame)]. }
    assert (Hdirect : D.leq direct (R.sigma_value next (R.frame_owner fr)) = true).
    { eapply DL.leq_trans; [exact (proj2 Hinput) |exact (@commit_sound st fr direct next next_fr Hset)]. }
    eapply eqv_trans; [|eapply eqv_trans; [exact Hfixed |apply eqv_sym; exact Hsame]].
    eapply (narrow_equiv (R.frame_owner fr)); [exact Hsafe |exact Hdirect |exact Hbelow |exact Hsame |apply eqv_sym; exact Hinput].
  - pose proof (@uncontrolled_commit_value st fr direct next next_fr Hcontrolled Hset) as Hvalue.
    assert (Heq : eqv (R.sigma_value next (R.frame_owner fr)) direct) by (eapply eqv_trans; eauto).
    split; [apply narrow_upper; exact (proj2 Heq) |].
    eapply DL.leq_trans; [exact (proj1 Heq) |apply narrow_lower; exact (proj2 Heq)].
Qed.
Definition precision_result tf st owner := exists result, Sem.rhs_observes (tf owner) result /\
  watched_reads st owner (Sem.observed_reads result) /\ eqv (narrow (R.sigma_value st owner) (Sem.observed_direct result)) (R.sigma_value st owner).
Definition precision_invariant tf c := forall owner, solved (R.cfg_state c) owner -> incoming_ready c owner -> precision_result tf (R.cfg_state c) owner.
Lemma precision_moved tf before after owner : frame_snapshot before after [owner] ->
  ~ In owner (R.queue after) -> precision_result tf before owner -> precision_result tf after owner.
Proof.
  intros Hview Hquiet [result [Htrace [Hreads Hfixed]]]; exists result; split; [exact Htrace |]; split.
  - exact (snapshot_reads Hview (or_introl eq_refl) _ ltac:(intros _; exact Hreads) Hquiet).
  - rewrite (snapshot_values Hview (or_introl eq_refl)); exact Hfixed.
Qed.
Lemma committing_precision tf roots before after owner : Features.recompute_controlled = true ->
  monotonic_system tf -> no_side_effects tf -> reachable tf roots before -> step tf before after ->
  committing before owner -> incoming_ready after owner -> precision_result tf (R.cfg_state after) owner.
Proof.
  intros Hon Hmono Hpure Hreachable Hstep [fr [direct [k [Hcontrol Howner]]]] [Hquiet _]; subst owner.
  destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in *; subst ctrl.
  pose proof (@reachable_semantic_invariant tf roots _ Hreachable) as Hsem.
  destruct (invariant_observing Hsem) as [[Hcursor Hstack]].
  destruct Hcursor as [reads sides spawns Hprefix Hwatches Hraw Hledger Hspawns].
  pose proof (@ordinary_phase_frontiers tf roots _ Hmono Hpure Hreachable (R.frame_owner fr) (R.frame_phase fr) (@phase_commit fr direct k)) as [Hsafe _].
  unfold step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset; inversion Hstep; subst after.
  exists {| Sem.Observation.observed_direct := direct; Sem.Observation.observed_reads := reads;
    Sem.Observation.observed_sides := sides; Sem.Observation.observed_spawns := spawns |}; split; [apply prefix_return; exact Hprefix |]; split.
  - eapply quiet_layout with (before := next); [reflexivity |reflexivity |apply requeue_keeps_queue | |exact Hquiet].
    exact (@quiet_set st fr direct next next_fr Hset (R.frame_owner fr) reads Hwatches).
  - exact (@ordinary_quiet_commit_fixed tf roots st fr direct k next next_fr Hon Hpure Hreachable Hsafe Hset Hquiet).
Qed.
Lemma committing_dec c owner : {committing c owner} + {~ committing c owner}.
Proof.
  destruct (R.cfg_control c) as [|seeds|seeds|child k|fr body k|fr direct pending k|fr direct k|fr k|k] eqn:Hcontrol.
  all: try solve [right; intros [frame [value [rest [Hbefore _]]]]; rewrite Hcontrol in Hbefore; discriminate].
  destruct (V.eq_dec owner (R.frame_owner fr)) as [Heq|Hneq].
  - left; exists fr, direct, k; auto.
  - right; intros [frame [value [rest [Hbefore Heq]]]]; rewrite Hcontrol in Hbefore; inversion Hbefore; subst; contradiction.
Qed.
Theorem next_precision_invariant tf roots before after : Features.recompute_controlled = true ->
  monotonic_system tf -> no_side_effects tf -> reachable tf roots before -> precision_invariant tf before ->
  step tf before after -> precision_invariant tf after.
Proof.
  intros Hon Hmono Hpure Hreachable Hprecision Hstep owner Hsolved Hready.
  destruct (committing_dec before owner) as [Hcommit|Hnot].
  - eapply committing_precision; eauto.
  - pose proof (@reachable_semantic_invariant tf roots before Hreachable) as Hsem.
    assert (Hold_solved : solved (R.cfg_state before) owner) by (eapply ready_solved_before; eauto using invariant_frames, invariant_waiting).
    pose proof (@next_incoming_origin tf before after (@reachable_owners_unique tf roots after (reachable_advance Hreachable Hstep)) Hstep owner Hready)
      as [Hbefore|Hcommit]; [|contradiction].
    eapply precision_moved; [eapply ordinary_ready_snapshot; eauto; exact (proj1 Hbefore) |exact (proj1 Hready) |apply Hprecision; assumption].
Qed.

Theorem ordinary_precision tf roots c : Features.recompute_controlled = true -> monotonic_system tf -> no_side_effects tf ->
  reachable tf roots c -> precision_invariant tf c.
Proof.
  intros Hon Hmono Hpure Hpath.
  assert (Hinitial : precision_invariant tf (R.initial_config roots)).
  { intros owner [value Hlookup] _; change (M.lookup (M.empty D.t) owner = Some value) in Hlookup; rewrite ML.lookup_empty in Hlookup; discriminate. }
  assert (Hpreserve : forall a b, steps tf a b -> reachable tf roots a -> precision_invariant tf a -> precision_invariant tf b).
  { intros a b Hsteps; induction Hsteps; intros Hreachable Hfirst; auto.
    apply IHHsteps; [eapply reachable_advance; eauto |eapply next_precision_invariant; eauto]. }
  exact (Hpreserve _ _ Hpath (@steps_refl tf (R.initial_config roots)) Hinitial).
Qed.
Definition narrowing_fixed := narrowing_fixed_with narrow (fun _ _ direct => direct).
Theorem successful_run_fixed fuel tf roots final : Features.recompute_controlled = true ->
  monotonic_system tf -> no_side_effects tf -> R.solve_fuel fuel tf roots = Some final -> narrowing_fixed tf final.
Proof.
  intros Hon Hmono Hpure Hrun; destruct (@successful_path fuel tf roots final Hrun) as [Hpath Hqueue].
  pose proof (@ordinary_precision tf roots (terminal final) Hon Hmono Hpure Hpath) as Hprecision.
  intros owner Hsolved; assert (Hready : incoming_ready (terminal final) owner).
  { split; [change (~ In owner (R.queue final)); rewrite Hqueue; tauto |left; cbn [terminal R.cfg_control active_owners]; tauto]. }
  destruct (Hprecision owner Hsolved Hready) as [result [Htrace [Hreads Hfixed]]].
  assert (Hat : Sem.observes_at (R.sigma_value final) (tf owner) result).
  { split; [exact Htrace |intros target value Hin; symmetry; apply read_value; exact (proj1 (Hreads target value Hin))]. }
  split.
  - exists (Sem.observed_direct result), (Sem.observed_reads result), (Sem.observed_sides result).
    apply observation_replay; [exact Htrace |intros target value Hin; exact (proj1 (Hreads target value Hin))].
  - intros direct reads effects Hreplay; destruct (replay_observation Hreplay) as [other [Hother [Hd [Hr He]]]].
    assert (Heq : result = other) by (eapply observation_unique; eauto); subst other.
    cbn; rewrite <- Hd; exact Hfixed.
Qed.
Theorem total_fixed tf roots : Features.recompute_controlled = true ->
  Sem.finite_system tf roots -> monotonic_system tf -> no_side_effects tf ->
  exists fuel final, R.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final /\ narrowing_fixed tf final.
Proof.
  intros Hon Hfinite Hmono Hpure; destruct (total_correct Hfinite) as [fuel [final [Hrun Hcorrect]]].
  exists fuel, final; split; [exact Hrun |]; split; [exact Hcorrect |eapply successful_run_fixed; eauto].
Qed.
End OrdinaryFixedness.
End OrdinaryPhases.
End OrdinaryDiscovery.

End Make.
