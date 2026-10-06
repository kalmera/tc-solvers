From Stdlib Require Import List Bool Lia Arith.PeanoNat Sorting.Permutation Sorting.Sorted.
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
Definition known support st x := In x support /\ ranked (R.ranking st) x.
Record store_wf support st := {
  store_valid : RL.valid (R.ranking st);
  store_generated : RF.generated support (R.ranking st);
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
  - apply RF.generated_empty.
  - apply references_empty.
  - constructor.
  - constructor.
Qed.
Lemma store_observe support st target : store_wf support st -> In target support ->
  store_wf support (R.observe st target) /\ known support (R.observe st target) target.
Proof.
  intros H Htarget; destruct (observe_order st target) as [Hext [Hrank Hvalid]].
  split; [constructor |split; auto].
  - exact (Hvalid (store_valid H)).
  - unfold R.observe; destruct (Ranks.observe (R.ranking st) target) eqn:Hobs; cbn.
    eapply RF.generated_observe; eauto using store_generated.
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
  - exact (store_generated H).
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
  - rewrite Hrank; exact (store_generated H).
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
  stack_refs (known support before) (fun x => In x support) k ->
  stack_refs (known support after) (fun x => In x support) k.
Proof. intros Hr Hk; eapply stack_weaken; [|exact Hk]; unfold known; rewrite Hr; auto. Qed.
Lemma materialize_rank st owner : R.ranking (R.materialize st owner) = R.ranking st.
Proof. unfold R.materialize; destruct (M.lookup _ owner); reflexivity. Qed.
Lemma close_rank st owner : R.ranking (R.reset_registered_cells st owner) = R.ranking st.
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity. Qed.
Definition config_wf support c := store_wf support (R.cfg_state c) /\
  control_refs (known support (R.cfg_state c)) (fun x => In x support) (R.cfg_control c).
Arguments store_observe {support st target} _ _.
Arguments store_get {support st fr target next next_fr value} _ _ _ _.
Arguments store_write {support st fr target input next changed} _ _ _ _.
Arguments get_layout {st fr target next next_fr value} _.
Arguments write_layout {st fr target input next changed} _.
Lemma continuation_side_wf support st fr target next k changed :
  store_wf support st -> frame_refs (known support st) fr -> known support st target ->
  Sem.rhs_supported (fun x => In x support) next ->
  stack_refs (known support st) (fun x => In x support) k ->
  config_wf support (R.continue_side st fr target next k changed).
Proof.
  intros Hst Hfr Htarget Hcode Hk; unfold R.continue_side;
    destruct changed; [destruct (_ && _)%bool |]; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs];
    auto using store_enqueue; tauto.
Qed.
Lemma continuation_dead_wf support st fr direct target pending k changed :
  store_wf support st -> frame_refs (known support st) fr -> known support st target ->
  Forall (known support st) pending -> stack_refs (known support st) (fun x => In x support) k ->
  config_wf support (R.continue_dead st fr direct target pending k changed).
Proof.
  intros Hst Hfr Htarget Hpending Hk; unfold R.continue_dead;
    destruct changed; [destruct (_ && _)%bool |]; split; cbn [R.cfg_state R.cfg_control control_refs stack_refs];
    auto using store_enqueue; tauto.
Qed.
Lemma observed_context support st target fr k :
  store_wf support st -> In target support ->
  frame_refs (known support st) fr -> stack_refs (known support st) (fun x => In x support) k ->
  store_wf support (R.observe st target) /\ known support (R.observe st target) target /\
  frame_refs (known support (R.observe st target)) fr /\
  stack_refs (known support (R.observe st target)) (fun x => In x support) k.
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
  (forall owner, In owner support -> Sem.rhs_supported (fun x => In x support) (tf owner)) ->
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
  steps tf (R.initial_config roots) c -> config_wf (Sem.support finite) c.
Proof.
  intro Hpath; assert (Hinitial : config_wf (Sem.support finite) (R.initial_config roots)).
  { split; [apply store_initial |].
    cbn [R.cfg_state R.cfg_control control_refs stack_refs]; apply Forall_forall; apply Sem.initial_supported. }
  revert Hinitial; induction Hpath; auto; intro Hfirst; apply IHHpath.
  eapply next_configuration_wf; eauto using Sem.system_supported.
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
  config_wf support before -> bounded_config upper before -> step tf before after -> bounded_config upper after.
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
  assert (Hwf : config_wf (Sem.support finite) (R.initial_config roots)) by (eapply reachable_configuration_wf; constructor).
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
  pose proof (@active_references (known support (R.cfg_state before)) (fun x => In x support)
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
Theorem reachable_active_ordered tf roots (finite : Sem.finite_system tf roots) c :
  steps tf (R.initial_config roots) c -> active_ordered c.
Proof.
  intro Hpath; assert (Hinitial : active_ordered (R.initial_config roots)) by constructor.
  assert (Hwf : config_wf (Sem.support finite) (R.initial_config roots)) by (eapply reachable_configuration_wf; constructor).
  revert Hwf Hinitial; induction Hpath; auto; intros Hwf Hsorted; apply IHHpath.
  - eapply next_configuration_wf; eauto using Sem.system_supported.
  - eapply next_active_ordered; eauto.
Qed.
Lemma ordered_unique order owners : ordered order owners -> NoDup owners.
Proof.
  intro H; induction H; constructor; auto.
  intro Hin; rewrite Forall_forall in H0; pose proof (H0 a Hin) as Haa; rewrite lt_irrefl in Haa; discriminate.
Qed.
Corollary reachable_owners_unique tf roots (finite : Sem.finite_system tf roots) c :
  steps tf (R.initial_config roots) c -> NoDup (active_owners (R.cfg_control c)).
Proof. intro H; apply (@ordered_unique (R.ranking (R.cfg_state c))); exact (@reachable_active_ordered tf roots finite c H). Qed.

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

(** The correctness premise is explicit until the new final-state invariant is
    finished; this lemma must not be presented as total leastness. *)
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

(** This is a local commit lemma, not yet final-state fixedness. The semantic
    invariant must still retain this commit observation until the final store. *)
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

End Make.
