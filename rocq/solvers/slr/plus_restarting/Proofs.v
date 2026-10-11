From Stdlib Require Import List Bool Lia Arith.PeanoNat Sorting.Sorted
  Sorting.Permutation Wellfounded Wf_nat.
From TcSolvers Require Import common.Assumptions common.ConstraintSemantics
  common.SourceStrictness common.SideUpdate common.FiniteHeight common.BoxUpdate
  common.SolverParameters
  solvers.slr.common.FirstActivation
  solvers.slr.reluctant_restarting.ReluctantRestartingInterfaces
  solvers.slr.plus_restarting.PlusRestarting.
Import ListNotations.
Set Implicit Arguments.

(** Fresh proofs of the deferred machine. All specifications and invariants
    use one machine instance; optional modules add laws without rebuilding it.
    Finite termination combines repeated-round credit descent with induction
    on discovery rank and finite outer scheduling. Successful runs establish
    correctness, leastness, ordinary fallback avoidance and narrowing fixedness
    without requiring value idempotency. *)
Module Make (V : VAR) (D : DOMAIN) (U : UPDATE V D) (SU : SIDE_UPDATE V D)
  (S : SET V) (M : MAP V) (Features : PlusRestarting.FEATURES)
  (DL : DOMAIN_LAWS D)
  (OSL : ORDINARY_UPDATE_SOUND_LAWS V D U)
  (SSL : SIDE_UPDATE_SOUND_LAWS V D SU)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

Module Ranks := ListDiscoveryOrder V.
Module RankLaws := FirstActivationLaws V.
Module RankFinite := ListFiniteDiscoveryOrderLaws V.
Module Solver := PlusRestarting.Interface V D U SU S M Ranks Features.
Module R := Solver.R.
Module Syntax := Solver.Syntax.
Module TransferSemantics := Solver.TransferSemantics.
Module ExecutionSemantics := Solver.ExecutionSemantics.
Module Sem.
  Module ConstraintSyntax := Syntax.
  Module R := R.
  Include TransferSemantics.
  Include ExecutionSemantics.
  Definition quiescent := Solver.Execution.quiescent.
  Definition terminal_config := Solver.Execution.terminal_config.
  Definition terminates_to tf roots final :=
    steps tf (R.initial_config roots) (terminal_config final) /\ quiescent final.
  Module Spec := SolverSpecifications.Make V D Solver.Sem Solver.View.
  Definition solved := Spec.solved.
  Definition state_valuation st : valuation := R.sigma_value st.
  Definition rhs_eval := Spec.replay.
  Definition side_effects_below := Spec.side_effects_below.
  Definition rhs_post_solution := Spec.rhs_post_solution.
  Definition correct_final_state := Spec.correct_final_state.
  Definition totally_correct_on tf roots := exists fuel final,
    R.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final.
End Sem.
Module Spec := Sem.Spec.
Include Spec.

Module Strict := SourceStrictness.Make V D DL.
Definition source_strict_on := Strict.source_strict_on
  Sem.observes_at Sem.observed_direct Sem.observed_sides.

Lemma path_join tf a b c : Sem.steps tf a b -> Sem.steps tf b c -> Sem.steps tf a c.
Proof. intros H; induction H; eauto using Sem.steps. Qed.
Lemma path_extend tf a b c : Sem.steps tf a b -> Sem.step tf b c -> Sem.steps tf a c.
Proof. intros; eapply path_join; eauto using Sem.steps. Qed.
Lemma run_path fuel tf c : Sem.steps tf c (R.run_fuel fuel tf c).
Proof.
  revert c; induction fuel; intro c; cbn; [constructor|].
  destruct (R.next_config tf c) eqn:E; eauto using Sem.steps.
Qed.
Lemma path_run tf a b : Sem.steps tf a b -> exists fuel, R.run_fuel fuel tf a = b.
Proof.
  intro H; induction H as [c|a b c Hab Hbc [n Hn]].
  - exists 0; reflexivity.
  - exists (S n). cbn. unfold Sem.step in Hab. now rewrite Hab.
Qed.
Lemma halted_shape c st : R.terminal_state c = Some st ->
  c = Sem.terminal_config st /\ Sem.quiescent st.
Proof.
  destruct c as [before ctrl], ctrl; cbn; try discriminate.
  destruct (R.queue before) eqn:Hq; cbn; try discriminate.
  destruct (R.deferred_wakes before) eqn:Hw; cbn; try discriminate.
  destruct (R.pending_spawns before) eqn:Hp; cbn; try discriminate.
  intro E; inversion E; subst; split; [reflexivity|repeat split; assumption].
Qed.
Lemma successful_path fuel tf roots st : R.solve_fuel fuel tf roots = Some st ->
  Sem.terminates_to tf roots st.
Proof.
  intro H; apply halted_shape in H as [E Hquiet]. split; [|exact Hquiet].
  rewrite <- E. apply run_path.
Qed.
Lemma run_append n m tf c : R.run_fuel (n + m) tf c = R.run_fuel m tf (R.run_fuel n tf c).
Proof.
  revert c; induction n; intro c; cbn; [reflexivity|].
  destruct (R.next_config tf c) eqn:E; [apply IHn|].
  clear IHn. induction m; cbn; [reflexivity|now rewrite E].
Qed.
Lemma terminal_stops tf st : Sem.quiescent st -> R.next_config tf (Sem.terminal_config st) = None.
Proof.
  intros [Hq [_ Hp]]. unfold Sem.terminal_config, R.next_config; cbn.
  now rewrite Hq, Hp.
Qed.
Lemma run_halted n tf c : R.next_config tf c = None -> R.run_fuel n tf c = c.
Proof. induction n; intro H; cbn; [reflexivity|now rewrite H]. Qed.
Lemma successful_more_fuel fuel tf roots st extra : R.solve_fuel fuel tf roots = Some st ->
  R.solve_fuel (fuel + extra) tf roots = Some st.
Proof.
  intro H. pose proof H as Hshape. unfold R.solve_fuel in Hshape.
  apply halted_shape in Hshape as [E Hquiet]. unfold R.solve_fuel.
  rewrite run_append, E, run_halted by now apply terminal_stops.
  unfold Sem.quiescent in Hquiet; destruct Hquiet as [Hq [Hw Hp]].
  unfold Sem.terminal_config, R.terminal_state; cbn; now rewrite Hq, Hw, Hp.
Qed.

Definition eqv a b := D.leq a b = true /\ D.leq b a = true.
(** A finite successful trace can check any invariant on every reachable
    configuration, including reachability after the fuel bound. *)
Theorem successful_trace_checks fuel tf roots final (property : R.config -> Prop) :
  R.solve_fuel fuel tf roots = Some final -> property (Sem.terminal_config final) ->
  Forall property (map (fun n => R.run_fuel n tf (R.initial_config roots)) (seq 0 fuel)) ->
  forall c, Sem.steps tf (R.initial_config roots) c -> property c.
Proof.
  intros Hrun Hfinal Hchecked c Hreach; destruct (path_run Hreach) as [n <-].
  destruct (Nat.lt_ge_cases n fuel) as [Hsmall|Hlarge].
  - apply (proj1 (Forall_forall _ _) Hchecked).
    apply in_map_iff; exists n; split; [reflexivity|apply in_seq; lia].
  - replace n with (fuel + (n - fuel)) by lia; rewrite run_append.
    apply halted_shape in Hrun as [E Hquiet]; rewrite E,run_halted by now apply terminal_stops.
    exact Hfinal.
Qed.

Fixpoint trace_check fuel tf (check : R.config -> bool) c : bool :=
  if check c then
    match fuel with
    | 0 => true
    | S rest => match R.next_config tf c with Some next => trace_check rest tf check next | None => true end
    end
  else false.
Lemma trace_check_at tf check (property : R.config -> Prop) :
  (forall c, check c = true -> property c) -> forall fuel c n, n <= fuel ->
  trace_check fuel tf check c = true -> property (R.run_fuel n tf c).
Proof.
  intros Hsound fuel; induction fuel as [|fuel IH]; intros c n Hbound Hchecked.
  - assert (n = 0) by lia; subst n; cbn in *; destruct (check c) eqn:E; [now apply Hsound|discriminate].
  - cbn [trace_check] in Hchecked; destruct (check c) eqn:E; [|discriminate].
    destruct n; [now apply Hsound|]; cbn [R.run_fuel].
    destruct (R.next_config tf c); [apply IH; [lia|exact Hchecked]|now apply Hsound].
Qed.
Theorem checked_successful_trace fuel tf roots final check (property : R.config -> Prop) :
  (forall c, check c = true -> property c) ->
  R.solve_fuel fuel tf roots = Some final -> trace_check fuel tf check (R.initial_config roots) = true ->
  forall c, Sem.steps tf (R.initial_config roots) c -> property c.
Proof.
  intros Hsound Hrun Hchecked; apply (@successful_trace_checks fuel tf roots final property Hrun).
  - apply halted_shape in Hrun as [<- _]; exact (@trace_check_at tf check property Hsound fuel _ fuel (Nat.le_refl _) Hchecked).
  - apply Forall_forall; intros c Hin; apply in_map_iff in Hin as [n [<- Hn]]; apply in_seq in Hn.
    exact (@trace_check_at tf check property Hsound fuel _ n (ltac:(lia)) Hchecked).
Qed.

Lemma eqv_refl a : eqv a a.
Proof. split; apply DL.leq_refl. Qed.
Lemma eqv_sym a b : eqv a b -> eqv b a.
Proof. unfold eqv; tauto. Qed.
Lemma eqv_trans a b c : eqv a b -> eqv b c -> eqv a c.
Proof. intros [H1 H2] [H3 H4]; split; eapply DL.leq_trans; eassumption. Qed.
Lemma equivalent_true a b : R.equivalent a b = true <-> eqv a b.
Proof. apply andb_true_iff. Qed.
Lemma equivalent_false a b : R.equivalent a b = false <-> ~ eqv a b.
Proof.
  destruct (R.equivalent a b) eqn:E; split; intro H; try discriminate.
  - exfalso; apply H. now apply equivalent_true.
  - intro Hq; apply equivalent_true in Hq; congruence.
  - reflexivity.
Qed.
Lemma join_upper a b c : D.leq a c = true -> D.leq b c = true -> D.leq (D.join a b) c = true.
Proof. apply DL.join_least. Qed.
Lemma join_mono a a' b b' : D.leq a a' = true -> D.leq b b' = true ->
  D.leq (D.join a b) (D.join a' b') = true.
Proof.
  intros; apply join_upper; eapply DL.leq_trans;
    eauto using DL.join_upper_left, DL.join_upper_right.
Qed.
Lemma join_congruent a a' b b' : eqv a a' -> eqv b b' -> eqv (D.join a b) (D.join a' b').
Proof. intros [H1 H2] [H3 H4]; split; apply join_mono; assumption. Qed.
Lemma join_bottom_right a : eqv (D.join a D.bottom) a.
Proof. split; auto using DL.join_least, DL.leq_refl, DL.bottom_least, DL.join_upper_left. Qed.
Lemma join_values_bound xs upper : D.leq (R.join_values xs) upper = true <->
  forall x, In x xs -> D.leq x upper = true.
Proof.
  induction xs as [|head rest IH]; cbn.
  - split; [intros _ x H; contradiction|intros _; apply DL.bottom_least].
  - split.
    + intros H x [<-|Hin].
      * eapply DL.leq_trans; [apply DL.join_upper_left|exact H].
      * apply (proj1 IH); [|exact Hin].
        eapply DL.leq_trans; [apply DL.join_upper_right|exact H].
    + intro H; apply DL.join_least; [apply H; now left|].
      apply IH; intros x Hin; apply H; now right.
Qed.

Lemma queue_contains_spec x q : R.queue_contains x q = true <-> In x q.
Proof.
  induction q as [|head rest IH]; cbn; [split; [discriminate|contradiction]|].
  destruct (V.eq_dec x head); subst; [tauto|]. rewrite IH. intuition congruence.
Qed.
Lemma queue_fresh_members order x q y :
  In y (R.queue_insert_fresh order x q) <-> y = x \/ In y q.
Proof.
  induction q as [|head rest IH]; cbn; [intuition congruence|].
  destruct (R.ranking_lt order head x); cbn; intuition congruence.
Qed.
Lemma queue_insert_members order x q y :
  In y (R.queue_insert order x q) <-> y = x \/ In y q.
Proof.
  unfold R.queue_insert; destruct (R.queue_contains x q) eqn:E.
  - apply queue_contains_spec in E; intuition congruence.
  - apply queue_fresh_members.
Qed.
Lemma queue_many_members order xs q y :
  In y (R.queue_insert_all order xs q) <-> In y xs \/ In y q.
Proof.
  revert q; induction xs as [|head rest IH]; intro q; cbn; [tauto|].
  rewrite IH, queue_insert_members; intuition congruence.
Qed.
Lemma queue_remove_members x q y : In y (R.queue_remove x q) -> In y q.
Proof.
  induction q as [|head rest IH]; cbn; [tauto|].
  destruct (V.eq_dec x head); cbn; intuition.
Qed.
Lemma queue_remove_other x q y : x <> y -> In y q -> In y (R.queue_remove x q).
Proof.
  induction q as [|head rest IH]; cbn; [tauto|].
  destruct (V.eq_dec x head); subst; cbn; intuition congruence.
Qed.
Lemma queue_fresh_distinct order x q : ~ In x q -> NoDup q -> NoDup (R.queue_insert_fresh order x q).
Proof.
  induction q as [|head rest IH]; cbn; intros Hx Hq; [constructor; [tauto|constructor]|].
  inversion Hq; subst; destruct (R.ranking_lt order head x); cbn.
  - constructor; assumption.
  - constructor; [rewrite queue_fresh_members; intuition|apply IH; tauto].
Qed.
Lemma queue_insert_distinct order x q : NoDup q -> NoDup (R.queue_insert order x q).
Proof.
  unfold R.queue_insert; destruct (R.queue_contains x q) eqn:E; intro H; [exact H|].
  apply queue_fresh_distinct; [intro Hin; apply queue_contains_spec in Hin; congruence|exact H].
Qed.
Lemma queue_many_distinct order xs q : NoDup q -> NoDup (R.queue_insert_all order xs q).
Proof. revert q; induction xs; cbn; intros; auto using queue_insert_distinct. Qed.

Definition store_view a b := R.sigma a = R.sigma b /\ R.dormant_bottom a = R.dormant_bottom b.
Lemma lookup_view a b x : store_view a b -> R.semantic_lookup a x = R.semantic_lookup b x.
Proof. intros [H1 H2]; unfold R.semantic_lookup; now rewrite H1, H2. Qed.
Lemma solved_view a b x : store_view a b -> solved a x <-> solved b x.
Proof. intro H; unfold solved, Sem.solved; now rewrite (lookup_view x H). Qed.
Lemma solved_cases st x : solved st x <->
  (exists v, M.lookup (R.sigma st) x = Some v) \/ S.mem x (R.dormant_bottom st) = true.
Proof.
  unfold solved, Sem.solved, R.semantic_lookup.
  destruct (M.lookup (R.sigma st) x) eqn:E; [split; intros; eauto|].
  destruct (S.mem x (R.dormant_bottom st)); split; intros; eauto; try discriminate.
  destruct H as [[v H]|H]; discriminate.
Qed.
Lemma solved_value st x : solved st x -> R.semantic_lookup st x = Some (R.sigma_value st x).
Proof.
  unfold solved, Sem.solved, R.semantic_lookup, R.sigma_value.
  intro H; destruct (M.lookup (R.sigma st) x); [reflexivity|].
  destruct (S.mem x (R.dormant_bottom st)); [reflexivity|destruct H as [v H]; discriminate].
Qed.
Lemma sigma_write_same st x v : R.sigma_value (R.with_sigma st (M.update (R.sigma st) x v)) x = v.
Proof. unfold R.sigma_value; cbn; now rewrite ML.lookup_update_same. Qed.
Lemma sigma_write_other st x y v : x <> y ->
  R.sigma_value (R.with_sigma st (M.update (R.sigma st) x v)) y = R.sigma_value st y.
Proof. intro H; unfold R.sigma_value; cbn; now rewrite ML.lookup_update_other by congruence. Qed.
Lemma sigma_write_solves st x v : solved (R.with_sigma st (M.update (R.sigma st) x v)) x.
Proof. apply solved_cases; left; cbn; eexists; apply ML.lookup_update_same. Qed.
Lemma sigma_write_preserves st x y v : solved st y -> solved (R.with_sigma st (M.update (R.sigma st) x v)) y.
Proof.
  rewrite !solved_cases; cbn; intro H; destruct (V.eq_dec y x); subst.
  - left; eexists; apply ML.lookup_update_same.
  - rewrite ML.lookup_update_other by assumption; exact H.
Qed.
Lemma dormant_solves st x : solved (R.remember_dormant st x) x.
Proof. apply solved_cases; right; cbn; apply SL.add_spec; now left. Qed.
Lemma dormant_preserves st x y : solved st y -> solved (R.remember_dormant st x) y.
Proof.
  rewrite !solved_cases; cbn; intros [H|H]; [now left|].
  right; apply SL.add_spec; now right.
Qed.
Lemma materialize_solves st x : solved (R.materialize st x) x.
Proof.
  unfold R.materialize; destruct (M.lookup (R.sigma st) x) eqn:E.
  - apply solved_cases; left; eauto.
  - apply sigma_write_solves.
Qed.
Lemma materialize_preserves st x y : solved st y -> solved (R.materialize st x) y.
Proof. unfold R.materialize; destruct (M.lookup _ _); auto using sigma_write_preserves. Qed.
Lemma materialize_valuation st x y : R.sigma_value (R.materialize st x) y = R.sigma_value st y.
Proof.
  unfold R.materialize; destruct (M.lookup (R.sigma st) x) eqn:E; [reflexivity|].
  destruct (V.eq_dec x y); subst.
  - rewrite sigma_write_same; unfold R.sigma_value; now rewrite E.
  - now apply sigma_write_other.
Qed.

(** Observations describe execution history without constraining the changing
    store. Replay is recovered only after all recorded reads are valid. *)
Lemma replay_observation st body direct reads sides : Sem.rhs_eval st body direct reads sides ->
  exists result, Sem.rhs_observes body result /\
    Sem.observed_direct result = direct /\ Sem.observed_reads result = reads /\
    Sem.observed_sides result = sides.
Proof.
  intro H; induction H.
  - eexists; split; [constructor|repeat split; reflexivity].
  - destruct IHrhs_eval_with as [result [Ht [Hd [Hr Hs]]]].
    exists {| Sem.Observation.observed_direct := Sem.observed_direct result;
      Sem.Observation.observed_reads := (target,value) :: Sem.observed_reads result;
      Sem.Observation.observed_sides := Sem.observed_sides result;
      Sem.Observation.observed_spawns := Sem.observed_spawns result |}.
    split; [constructor; exact Ht|cbn; repeat split; congruence].
  - destruct IHrhs_eval_with as [result [Ht [Hd [Hr Hs]]]].
    eexists; split; [constructor; exact Ht|cbn; repeat split; congruence].
  - destruct IHrhs_eval_with as [result [Ht [Hd [Hr Hs]]]].
    eexists; split; [constructor; exact Ht|cbn; repeat split; congruence].
Qed.
Lemma observation_replay st body result : Sem.rhs_observes body result ->
  (forall x v, In (x,v) (Sem.observed_reads result) -> R.semantic_lookup st x = Some v) ->
  Sem.rhs_eval st body (Sem.observed_direct result) (Sem.observed_reads result) (Sem.observed_sides result).
Proof.
  intro H; induction H as [direct|target value next result Htail IH|
    target value next result Htail IH|target next result Htail IH]; intro Hreads; cbn in *.
  - constructor.
  - constructor; [apply Hreads; now left|].
    apply IH; intros x v Hin; apply Hreads; now right.
  - constructor; apply IH; exact Hreads.
  - constructor; apply IH; exact Hreads.
Qed.
Lemma replay_unique st body d1 r1 s1 d2 r2 s2 :
  Sem.rhs_eval st body d1 r1 s1 -> Sem.rhs_eval st body d2 r2 s2 ->
  d1 = d2 /\ r1 = r2 /\ s1 = s2.
Proof.
  intro H; revert d2 r2 s2; induction H; intros d2 r2 s2 H2; inversion H2; subst.
  - repeat split; reflexivity.
  - match goal with
    | A : R.semantic_lookup st ?x = Some ?v,
      B : R.semantic_lookup st ?x = Some ?w |- _ => rewrite A in B; inversion B; subst
    end.
    match goal with T : Sem.rhs_eval_with _ (next _) _ _ _ |- _ =>
      destruct (IHrhs_eval_with _ _ _ T) as [-> [-> ->]] end.
    repeat split; reflexivity.
  - match goal with T : Sem.rhs_eval_with _ next _ _ _ |- _ =>
      destruct (IHrhs_eval_with _ _ _ T) as [-> [-> ->]] end.
    repeat split; reflexivity.
  - match goal with T : Sem.rhs_eval_with _ next _ _ _ |- _ =>
      destruct (IHrhs_eval_with _ _ _ T) as [-> [-> ->]] end.
    repeat split; reflexivity.
Qed.

Definition pending st owner := In owner (R.queue st) \/ In owner (R.deferred_wakes st).
Definition rank_extension a b := forall x n,
  Ranks.lookup (R.ranking a) x = Some n -> Ranks.lookup (R.ranking b) x = Some n.
Definition priority st x := match Ranks.lookup (R.ranking st) x with Some n => S n | None => 0 end.
Definition ranked st x := exists n, Ranks.lookup (R.ranking st) x = Some n.
Definition ranked_list st xs := Forall (ranked st) xs.
Definition sorted_queue st q := StronglySorted (fun x y => priority st y < priority st x) q.
Lemma rank_extension_refl st : rank_extension st st.
Proof. intros x n H; exact H. Qed.
Lemma rank_extension_trans a b c : rank_extension a b -> rank_extension b c -> rank_extension a c.
Proof. intros H1 H2 x n H; apply H2, H1, H. Qed.
Lemma ranked_extension a b x : rank_extension a b -> ranked a x -> ranked b x.
Proof. intros H [n E]; exists n; now apply H. Qed.
Lemma priority_extension a b x : rank_extension a b -> ranked a x -> priority a x = priority b x.
Proof. intros H [n E]; unfold priority; now rewrite E, (H x n E). Qed.
Lemma ranked_list_extension a b xs : rank_extension a b -> ranked_list a xs -> ranked_list b xs.
Proof. intros H; apply Forall_impl; intros x Hx; eapply ranked_extension; eauto. Qed.
Lemma observe_extends st x : rank_extension st (R.observe st x).
Proof.
  intros y n H; unfold R.observe; destruct (Ranks.observe (R.ranking st) x) as [order rank] eqn:E.
  cbn. exact (@RankLaws.observe_preserves _ _ _ _ _ _ E H).
Qed.
Lemma observe_ranks st x : ranked (R.observe st x) x.
Proof.
  unfold R.observe; destruct (Ranks.observe (R.ranking st) x) as [order n] eqn:E.
  exists n; cbn; exact (@RankLaws.observe_lookup _ _ _ _ E).
Qed.
Lemma compare_rank st x y : ranked st x -> ranked st y ->
  (R.rank_lt st x y = true <-> priority st x < priority st y).
Proof.
  intros [nx Hx] [ny Hy]; unfold R.rank_lt, R.ranking_lt, priority; rewrite Hx, Hy.
  rewrite Nat.ltb_lt; lia.
Qed.
Lemma compare_rank_false st x y : ranked st x -> ranked st y ->
  (R.rank_lt st x y = false <-> priority st y <= priority st x).
Proof.
  intros [nx Hx] [ny Hy]; unfold R.rank_lt, R.ranking_lt, priority; rewrite Hx, Hy.
  rewrite Nat.ltb_ge; lia.
Qed.
Lemma rank_lt_extension a b x y : rank_extension a b -> R.rank_lt a x y = true -> R.rank_lt b x y = true.
Proof.
  intros H; unfold R.rank_lt, R.ranking_lt.
  destruct (Ranks.lookup (R.ranking a) x) eqn:Hx,
    (Ranks.lookup (R.ranking a) y) eqn:Hy; try discriminate.
  now rewrite (H x _ Hx), (H y _ Hy).
Qed.
Lemma rank_valid_observe st x : RankLaws.valid (R.ranking st) -> RankLaws.valid (R.ranking (R.observe st x)).
Proof.
  intro H; unfold R.observe; destruct (Ranks.observe _ _) as [next n] eqn:E; cbn.
  eapply RankLaws.observe_valid; eauto.
Qed.
Lemma priority_distinct st x y : RankLaws.valid (R.ranking st) ->
  ranked st x -> ranked st y -> priority st x = priority st y -> x = y.
Proof.
  intros Hv [nx Hx] [ny Hy] Heq; unfold priority in Heq; rewrite Hx, Hy in Heq.
  inversion Heq; subst. eapply RankLaws.lookup_injective; eauto.
Qed.
Lemma sorted_queue_extension a b q : rank_extension a b -> ranked_list a q ->
  sorted_queue a q -> sorted_queue b q.
Proof.
  intros He Hr Ho; induction Ho as [|x q Hq IH Hbelow]; [constructor|].
  inversion Hr as [|? ? Hx Hrest]; subst.
  constructor; [apply IH; exact Hrest|].
  apply Forall_forall; intros y Hin.
  rewrite <- (priority_extension He Hx),
    <- (priority_extension He (proj1 (Forall_forall _ _) Hrest y Hin)).
  exact (proj1 (Forall_forall _ _) Hbelow y Hin).
Qed.
Lemma queue_fresh_sorted st x q : ranked st x -> ranked_list st q -> ~ In x q ->
  RankLaws.valid (R.ranking st) -> sorted_queue st q ->
  sorted_queue st (R.queue_insert_fresh (R.ranking st) x q).
Proof.
  intros Hx Hr Hfresh Hv Ho; revert Hr Hfresh.
  induction Ho as [|head rest Hsorted IH Hbelow]; intros Hr Hfresh; cbn.
  - constructor; constructor.
  - inversion Hr as [|? ? Hhead Hrest]; subst.
    destruct (R.ranking_lt (R.ranking st) head x) eqn:E.
    + constructor; [constructor; assumption|].
      apply Forall_cons; [now apply (proj1 (compare_rank Hhead Hx))|].
      apply Forall_forall; intros y Hin.
      change (priority st y < priority st x).
      eapply Nat.lt_trans; [exact (proj1 (Forall_forall _ _) Hbelow y Hin)|].
      exact (proj1 (compare_rank Hhead Hx) E).
    + constructor.
      * apply IH; [exact Hrest|intro H; apply Hfresh; now right].
      * apply Forall_forall; intros y Hin; apply queue_fresh_members in Hin as [->|Hin].
        -- change (priority st x < priority st head).
           pose proof (proj1 (compare_rank_false Hhead Hx) E).
           assert (priority st x <> priority st head).
           { intro Heq; apply Hfresh; left; symmetry; eapply priority_distinct; eauto. }
           lia.
        -- exact (proj1 (Forall_forall _ _) Hbelow y Hin).
Qed.
Lemma queue_insert_sorted st x q : ranked st x -> ranked_list st q ->
  RankLaws.valid (R.ranking st) -> sorted_queue st q ->
  sorted_queue st (R.queue_insert (R.ranking st) x q).
Proof.
  intros Hx Hr Hv Ho; unfold R.queue_insert; destruct (R.queue_contains x q) eqn:E; [exact Ho|].
  apply queue_fresh_sorted; auto. intro Hin; apply queue_contains_spec in Hin; congruence.
Qed.
Lemma queue_many_ranked st xs q : ranked_list st xs -> ranked_list st q ->
  ranked_list st (R.queue_insert_all (R.ranking st) xs q).
Proof.
  intros Hx Hq; apply Forall_forall; intros y Hin; apply queue_many_members in Hin as [Hin|Hin].
  - exact (proj1 (Forall_forall _ _) Hx y Hin).
  - exact (proj1 (Forall_forall _ _) Hq y Hin).
Qed.
Lemma queue_many_sorted st xs q : ranked_list st xs -> ranked_list st q ->
  RankLaws.valid (R.ranking st) -> sorted_queue st q ->
  sorted_queue st (R.queue_insert_all (R.ranking st) xs q).
Proof.
  revert q; induction xs as [|x xs IH]; cbn; intros q Hxs Hq Hv Ho; [exact Ho|].
  inversion Hxs as [|? ? Hx Hrest]; subst. apply IH; auto.
  - apply Forall_forall; intros y Hin; apply queue_insert_members in Hin as [->|Hin]; [exact Hx|].
    exact (proj1 (Forall_forall _ _) Hq y Hin).
  - now apply queue_insert_sorted.
Qed.
Lemma sorted_head_max st head tail y : sorted_queue st (head :: tail) ->
  In y (head :: tail) -> priority st y <= priority st head.
Proof.
  intros Hq [<-|Hy]; [lia|]. inversion Hq; subst.
  match goal with H : Forall _ tail |- _ =>
    pose proof (proj1 (Forall_forall _ _) H y Hy) as Below end.
  change (priority st y < priority st head) in Below; lia.
Qed.

Definition table_value {A} (table : M.t (M.t A)) outer inner :=
  M.lookup (R.lookup_map table outer) inner.
Lemma nested_write_same {A} table outer inner (v : A) :
  table_value (R.update_map table outer inner v) outer inner = Some v.
Proof. unfold table_value, R.update_map, R.lookup_map; rewrite ML.lookup_update_same; apply ML.lookup_update_same. Qed.
Lemma nested_write_inner {A} table outer inner other (v : A) : inner <> other ->
  table_value (R.update_map table outer inner v) outer other = table_value table outer other.
Proof.
  intro H; unfold table_value, R.update_map, R.lookup_map; rewrite ML.lookup_update_same.
  apply ML.lookup_update_other; congruence.
Qed.
Lemma nested_write_outer {A} table outer other inner key (v : A) : outer <> other ->
  table_value (R.update_map table outer inner v) other key = table_value table other key.
Proof.
  intro H; unfold table_value, R.update_map, R.lookup_map.
  now rewrite ML.lookup_update_other by congruence.
Qed.
Lemma contribution_le_aggregate st source target :
  D.leq (R.stored_contribution st source target) (R.aggregate st target) = true.
Proof.
  unfold R.stored_contribution, R.aggregate.
  destruct (M.lookup (R.lookup_map (R.contributions st) target) source) eqn:E.
  - apply (proj1 (join_values_bound _ _) (DL.leq_refl _)).
    eapply ML.lookup_values; exact E.
  - apply DL.bottom_least.
Qed.
Lemma aggregate_empty st : R.contributions st = M.empty (M.t D.t) ->
  forall target, R.aggregate st target = D.bottom.
Proof.
  intros E target; unfold R.aggregate, R.lookup_map; rewrite E, ML.lookup_empty, ML.values_empty; reflexivity.
Qed.
Lemma reader_mem_add st target owner x :
  S.mem x (R.lookup_set (R.readers (R.add_reader st target owner)) target) = true <->
  x = owner \/ S.mem x (R.lookup_set (R.readers st) target) = true.
Proof. unfold R.add_reader, R.lookup_set; cbn; rewrite ML.lookup_update_same; apply SL.add_spec. Qed.
Lemma reader_mem_other st target owner x y : target <> y ->
  S.mem x (R.lookup_set (R.readers (R.add_reader st target owner)) y) =
  S.mem x (R.lookup_set (R.readers st) y).
Proof. intro H; unfold R.add_reader, R.lookup_set; cbn; now rewrite ML.lookup_update_other by congruence. Qed.
Lemma request_preserves st target : R.sigma (R.request_spawn st target) = R.sigma st /\
  R.dormant_bottom (R.request_spawn st target) = R.dormant_bottom st /\
  R.ranking (R.request_spawn st target) = R.ranking st.
Proof. unfold R.request_spawn; destruct (S.mem _ _); repeat split; reflexivity. Qed.
Lemma request_members st target x : In x (R.pending_spawns (R.request_spawn st target)) ->
  x = target \/ In x (R.pending_spawns st).
Proof.
  unfold R.request_spawn; destruct (S.mem _ _); cbn; [tauto|].
  rewrite in_app_iff; cbn; intuition congruence.
Qed.
Lemma requested_add st target x :
  S.mem x (R.requested_spawns (R.request_spawn st target)) = true <->
  x = target \/ S.mem x (R.requested_spawns st) = true.
Proof.
  unfold R.request_spawn; destruct (S.mem target (R.requested_spawns st)) eqn:E; cbn.
  - intuition congruence.
  - apply SL.add_spec.
Qed.

(** The logical stack follows the executable continuation stack. Suspended
    owners remain active, so a fresh child cannot overwrite their side row. *)
Fixpoint suspended_owners k : list V.t :=
  match k with
  | R.KLoop | R.KSeedLoop _ => []
  | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest
  | R.KDead fr _ _ rest | R.KDrain fr rest => R.frame_owner fr :: suspended_owners rest
  end.
Definition active_owners ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => []
  | R.StartEpisode owner k => owner :: suspended_owners k
  | R.Return k => suspended_owners k
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k =>
      R.frame_owner fr :: suspended_owners k
  end.
Definition framed_owners ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => []
  | R.StartEpisode _ k | R.Return k => suspended_owners k
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k =>
      R.frame_owner fr :: suspended_owners k
  end.
Fixpoint suspended_seeds k : list V.t :=
  match k with
  | R.KLoop => []
  | R.KSeedLoop roots => roots
  | R.KAfterGet _ _ _ rest | R.KAfterSide _ _ rest | R.KAfterSpawn _ _ rest
  | R.KDead _ _ _ rest | R.KDrain _ rest => suspended_seeds rest
  end.
Definition seed_owners ctrl :=
  match ctrl with
  | R.RunLoop => []
  | R.RunSeeds roots | R.RunSeedLoop roots => roots
  | R.StartEpisode _ k | R.Return k | R.RunRhs _ _ k | R.RunDead _ _ _ k
  | R.RunCommit _ _ k | R.RunDrain _ k => suspended_seeds k
  end.
Definition busy c owner := pending (R.cfg_state c) owner \/ In owner (active_owners (R.cfg_control c)).
Definition demand c target :=
  solved (R.cfg_state c) target \/ busy c target \/ In target (seed_owners (R.cfg_control c)).
Definition ready c target := solved (R.cfg_state c) target \/ busy c target.
Definition spawn_accounted c target := demand c target \/
  S.mem target (R.requested_spawns (R.cfg_state c)) = true.
Definition read_guard st owner target value := pending st owner \/
  (R.semantic_lookup st target = Some value /\
   S.mem owner (R.lookup_set (R.readers st) target) = true).
Definition reads_guarded st owner events := forall target value,
  In (target,value) events -> read_guard st owner target value.
Definition emitted_below st owner events := forall target value,
  In (target,value) events -> D.leq value (R.stored_contribution st owner target) = true.
Definition spawns_accounted c targets := forall target, In target targets -> spawn_accounted c target.
Record saved_observation tf c owner result : Prop := {
  saved_trace : Sem.rhs_observes (tf owner) result;
  saved_reads : reads_guarded (R.cfg_state c) owner (Sem.observed_reads result);
  saved_sides : emitted_below (R.cfg_state c) owner (Sem.observed_sides result);
  saved_spawns : spawns_accounted c (Sem.observed_spawns result);
  saved_direct : D.leq (Sem.observed_direct result) (R.sigma_value (R.cfg_state c) owner) = true
}.
Definition summaries tf c := forall owner, solved (R.cfg_state c) owner ->
  busy c owner \/ exists result, saved_observation tf c owner result.
Definition contribution_bounds c := forall target, busy c target \/
  D.leq (R.aggregate (R.cfg_state c) target) (R.sigma_value (R.cfg_state c) target) = true.
Definition requests_accounted c := forall target,
  S.mem target (R.requested_spawns (R.cfg_state c)) = true ->
  In target (R.pending_spawns (R.cfg_state c)) \/ demand c target.
Definition seeds_accounted roots c := forall target, In target roots -> demand c target.

Inductive prefix root : Syntax.rhs -> list (V.t * D.t) -> list (V.t * D.t) -> list V.t -> Prop :=
| PrefixEmpty : prefix root root [] [] []
| PrefixRead target value next reads sides spawns :
    prefix root (Syntax.Get target next) reads sides spawns ->
    prefix root (next value) (reads ++ [(target,value)]) sides spawns
| PrefixSide target value next reads sides spawns :
    prefix root (Syntax.Side target value next) reads sides spawns ->
    prefix root next reads (sides ++ [(target,value)]) spawns
| PrefixSpawn target next reads sides spawns :
    prefix root (Syntax.Spawn target next) reads sides spawns ->
    prefix root next reads sides (spawns ++ [target]).
Definition append_observation reads sides spawns result : Sem.observation :=
  {| Sem.Observation.observed_direct := Sem.observed_direct result;
     Sem.Observation.observed_reads := reads ++ Sem.observed_reads result;
     Sem.Observation.observed_sides := sides ++ Sem.observed_sides result;
     Sem.Observation.observed_spawns := spawns ++ Sem.observed_spawns result |}.
Lemma prefix_observation root body reads sides spawns : prefix root body reads sides spawns ->
  forall result, Sem.rhs_observes body result ->
  Sem.rhs_observes root (append_observation reads sides spawns result).
Proof.
  intro H; induction H as [|target value next reads sides spawns Hp IH|
    target value next reads sides spawns Hp IH|target next reads sides spawns Hp IH];
    intros result Hresult.
  - destruct result; exact Hresult.
  - pose proof (IH _ (Sem.ObserveGet target value next Hresult)) as Hwhole.
    unfold append_observation in *; cbn in *; now rewrite <- app_assoc.
  - pose proof (IH _ (Sem.ObserveSide target value Hresult)) as Hwhole.
    unfold append_observation in *; cbn in *; now rewrite <- app_assoc.
  - pose proof (IH _ (Sem.ObserveSpawn target Hresult)) as Hwhole.
    unfold append_observation in *; cbn in *; now rewrite <- app_assoc.
Qed.
Lemma prefix_finish root direct reads sides spawns : prefix root (Syntax.Ret direct) reads sides spawns ->
  Sem.rhs_observes root
    {| Sem.Observation.observed_direct := direct;
       Sem.Observation.observed_reads := reads;
       Sem.Observation.observed_sides := sides;
       Sem.Observation.observed_spawns := spawns |}.
Proof.
  intro H; pose proof (prefix_observation H (Sem.ObserveRet direct)) as E.
  unfold append_observation in E; cbn in E; now rewrite !app_nil_r in E.
Qed.
Definition local_value fr target := match M.lookup (R.frame_local_side fr) target with
  Some value => value | None => D.bottom end.
Definition local_covers fr sides := forall target value,
  In (target,value) sides -> D.leq value (local_value fr target) = true.
Definition locals_published st fr := forall target,
  S.mem target (R.frame_current_targets fr) = true ->
  D.leq (local_value fr target) (R.stored_contribution st (R.frame_owner fr) target) = true.
Definition side_targets fr (sides : list (V.t * D.t)) := forall target,
  S.mem target (R.frame_current_targets fr) = true <-> exists value, In (target,value) sides.
Definition evaluation tf c fr body := exists reads sides spawns,
  prefix (tf (R.frame_owner fr)) body reads sides spawns /\
  reads_guarded (R.cfg_state c) (R.frame_owner fr) reads /\
  local_covers fr sides /\ locals_published (R.cfg_state c) fr /\
  side_targets fr sides /\ spawns_accounted c spawns.
Definition incoming_bound c owner := pending (R.cfg_state c) owner \/
  ~ In owner (framed_owners (R.cfg_control c)) \/
  D.leq (R.aggregate (R.cfg_state c) owner) (R.sigma_value (R.cfg_state c) owner) = true.
Definition completed tf c fr := exists result,
  saved_observation tf c (R.frame_owner fr) result /\ incoming_bound c (R.frame_owner fr).
Fixpoint continuation_valid tf c k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => True
  | R.KAfterGet fr target next rest =>
      evaluation tf c fr (Syntax.Get target next) /\ ready c target /\ continuation_valid tf c rest
  | R.KAfterSide fr next rest | R.KAfterSpawn fr next rest =>
      evaluation tf c fr next /\ continuation_valid tf c rest
  | R.KDead fr direct _ rest =>
      evaluation tf c fr (Syntax.Ret direct) /\ continuation_valid tf c rest
  | R.KDrain fr rest => completed tf c fr /\ continuation_valid tf c rest
  end.
Definition control_valid tf c :=
  match R.cfg_control c with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
  | R.StartEpisode _ k | R.Return k => continuation_valid tf c k
  | R.RunRhs fr body k => evaluation tf c fr body /\ continuation_valid tf c k
  | R.RunDead fr direct _ k | R.RunCommit fr direct k =>
      evaluation tf c fr (Syntax.Ret direct) /\ continuation_valid tf c k
  | R.RunDrain fr k => completed tf c fr /\ continuation_valid tf c k
  end.
Definition wakes_finished c :=
  match R.cfg_control c with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ | R.RunDrain _ _ | R.Return _ =>
      R.deferred_wakes (R.cfg_state c) = []
  | _ => True
  end.
Record machine_shape tf c : Prop := {
  shape_ranks : RankLaws.valid (R.ranking (R.cfg_state c));
  shape_materialized : forall x, R.is_materialized (R.cfg_state c) x = true -> ranked (R.cfg_state c) x;
  shape_dormant : forall x, S.mem x (R.dormant_bottom (R.cfg_state c)) = true -> R.pure_bottom_rhs tf x = true;
  shape_readers : forall target owner,
    S.mem owner (R.lookup_set (R.readers (R.cfg_state c)) target) = true -> ranked (R.cfg_state c) owner;
  shape_queue_ranks : ranked_list (R.cfg_state c) (R.queue (R.cfg_state c));
  shape_wake_ranks : ranked_list (R.cfg_state c) (R.deferred_wakes (R.cfg_state c));
  shape_queue_order : sorted_queue (R.cfg_state c) (R.queue (R.cfg_state c));
  shape_wake_order : sorted_queue (R.cfg_state c) (R.deferred_wakes (R.cfg_state c));
  shape_stack_ranks : ranked_list (R.cfg_state c) (active_owners (R.cfg_control c));
  shape_stack_order : sorted_queue (R.cfg_state c) (active_owners (R.cfg_control c));
  shape_live_frames : forall owner, In owner (framed_owners (R.cfg_control c)) -> solved (R.cfg_state c) owner;
  shape_wakes : wakes_finished c
}.
Record invariant tf roots c : Prop := {
  inv_shape : machine_shape tf c;
  inv_summaries : summaries tf c;
  inv_contributions : contribution_bounds c;
  inv_requests : requests_accounted c;
  inv_seeds : seeds_accounted roots c;
  inv_control : control_valid tf c
}.

Lemma read_guard_monotone a b owner target value :
  (pending a owner -> pending b owner) ->
  R.semantic_lookup b target = R.semantic_lookup a target ->
  (S.mem owner (R.lookup_set (R.readers a) target) = true ->
   S.mem owner (R.lookup_set (R.readers b) target) = true) ->
  read_guard a owner target value -> read_guard b owner target value.
Proof. unfold read_guard; intuition congruence. Qed.
Lemma read_guard_write a b target :
  (forall owner, pending a owner -> pending b owner) ->
  (forall x, x <> target -> R.semantic_lookup b x = R.semantic_lookup a x) ->
  (forall x owner, x <> target ->
    S.mem owner (R.lookup_set (R.readers a) x) = true ->
    S.mem owner (R.lookup_set (R.readers b) x) = true) ->
  (forall owner, S.mem owner (R.lookup_set (R.readers a) target) = true -> pending b owner) ->
  forall owner x value, read_guard a owner x value -> read_guard b owner x value.
Proof.
  intros Hp Hlookup Hreader Hw owner x value [Hpending|[Hvalue Hregistered]].
  - left; now apply Hp.
  - destruct (V.eq_dec x target); subst; [left; now apply Hw|].
    right; split; [now rewrite Hlookup|now apply Hreader].
Qed.
Lemma read_guard_forget a b owner :
  (forall x, x <> owner -> pending a x -> pending b x) ->
  (forall target, R.semantic_lookup b target = R.semantic_lookup a target) ->
  (forall target x, S.mem x (R.lookup_set (R.readers a) target) = true ->
    S.mem x (R.lookup_set (R.readers b) target) = true) ->
  forall x target value, x <> owner -> read_guard a x target value -> read_guard b x target value.
Proof.
  intros Hp Hl Hr x target value Hx Hg; eapply read_guard_monotone; [|apply Hl|apply Hr|exact Hg].
  apply Hp; exact Hx.
Qed.
Lemma guarded_reads_replay st owner events : ~ pending st owner -> reads_guarded st owner events ->
  forall target value, In (target,value) events -> R.semantic_lookup st target = Some value.
Proof. intros Hnot Hreads target value Hin; destruct (Hreads target value Hin) as [H|H]; tauto. Qed.
(** A checked prefix can consume a complete replay of the same transfer
    tree. This links a current evaluation to the semantic post-solution. *)
Lemma prefix_replay_direct st root body reads sides spawns : prefix root body reads sides spawns ->
  (forall target value, In (target,value) reads -> R.semantic_lookup st target = Some value) ->
  forall direct observed_reads effects, Sem.rhs_eval st root direct observed_reads effects ->
  exists remaining_reads remaining_effects, Sem.rhs_eval st body direct remaining_reads remaining_effects.
Proof.
  intro Hp; induction Hp as [|target value tail reads sides spawns Hp IH|
    target value tail reads sides spawns Hp IH|target tail reads sides spawns Hp IH]; intros Hreads direct observed_reads effects Hreplay.
  - eauto.
  - assert (Hbefore : forall key observed, In (key,observed) reads -> R.semantic_lookup st key = Some observed).
    { intros; apply Hreads; apply in_or_app; now left. }
    destruct (IH Hbefore direct observed_reads effects Hreplay) as [remaining_reads [remaining_effects Heval]].
    assert (Hvalue : R.semantic_lookup st target = Some value) by (apply Hreads; apply in_or_app; right; now left).
    inversion Heval; subst; match goal with
    | Hlookup : R.semantic_lookup st target = Some ?observed |- _ =>
        assert (observed = value) by congruence; subst observed
    end; eauto.
  - destruct (IH Hreads direct observed_reads effects Hreplay) as [remaining_reads [remaining_effects Heval]];
      inversion Heval; subst; eauto.
  - destruct (IH Hreads direct observed_reads effects Hreplay) as [remaining_reads [remaining_effects Heval]];
      inversion Heval; subst; eauto.
Qed.
Lemma prefix_replay_residual st root body reads sides spawns : prefix root body reads sides spawns ->
  (forall target value, In (target,value) reads -> R.semantic_lookup st target = Some value) ->
  (exists direct observed_reads effects, Sem.rhs_eval st root direct observed_reads effects) ->
  exists direct observed_reads effects, Sem.rhs_eval st body direct observed_reads effects.
Proof.
  intros Hp Hreads [direct [observed_reads [effects Hreplay]]].
  destruct (@prefix_replay_direct st root body reads sides spawns Hp Hreads direct observed_reads effects Hreplay)
    as [remaining_reads [remaining_effects Heval]]; eauto.
Qed.
Lemma evaluation_post_get_solved tf c fr target tail : ~ pending (R.cfg_state c) (R.frame_owner fr) ->
  evaluation tf c fr (Syntax.Get target tail) -> owner_post_solution tf (R.cfg_state c) (R.frame_owner fr) -> solved (R.cfg_state c) target.
Proof.
  intros Hquiet [reads [sides [spawns [Hp [Hreads _]]]]] [Hpost _].
  destruct (@prefix_replay_residual (R.cfg_state c) (tf (R.frame_owner fr)) (Syntax.Get target tail) reads sides spawns Hp
    (@guarded_reads_replay (R.cfg_state c) (R.frame_owner fr) reads Hquiet Hreads) Hpost)
    as [direct [observed_reads [effects Heval]]].
  inversion Heval; subst; unfold solved,Sem.solved; eauto.
Qed.
Lemma evaluation_post_ret_below tf c fr direct : ~ pending (R.cfg_state c) (R.frame_owner fr) ->
  evaluation tf c fr (Syntax.Ret direct) -> owner_post_solution tf (R.cfg_state c) (R.frame_owner fr) ->
  D.leq direct (R.sigma_value (R.cfg_state c) (R.frame_owner fr)) = true.
Proof.
  intros Hquiet [reads [sides [spawns [Hp [Hreads _]]]]] [[observed_direct [observed_reads [effects Hreplay]]] [Hpost _]].
  destruct (@prefix_replay_direct (R.cfg_state c) (tf (R.frame_owner fr)) (Syntax.Ret direct) reads sides spawns Hp
    (@guarded_reads_replay (R.cfg_state c) (R.frame_owner fr) reads Hquiet Hreads) observed_direct observed_reads effects Hreplay)
    as [remaining_reads [remaining_effects Heval]].
  inversion Heval; subst; exact (proj1 (Hpost _ _ _ Hreplay)).
Qed.

Lemma terminal_not_busy st owner : Sem.quiescent st -> ~ busy (Sem.terminal_config st) owner.
Proof. intros [Hq [Hw Hp]]; unfold busy, pending, Sem.terminal_config; cbn; rewrite Hq, Hw; tauto. Qed.
Lemma terminal_spawn_solved st target : Sem.quiescent st -> requests_accounted (Sem.terminal_config st) ->
  spawn_accounted (Sem.terminal_config st) target -> solved st target.
Proof.
  intros [Hq [Hw Hp]] Hrequested Hcovered.
  unfold requests_accounted in Hrequested.
  unfold spawn_accounted, demand, busy, pending, Sem.terminal_config, active_owners, seed_owners in *; cbn in *.
  specialize (Hrequested target).
  rewrite Hq, Hw, Hp in Hrequested; rewrite Hq, Hw in Hcovered; cbn in *; tauto.
Qed.
Lemma saved_terminal_replay tf st owner result : Sem.quiescent st ->
  saved_observation tf (Sem.terminal_config st) owner result ->
  Sem.rhs_eval st (tf owner) (Sem.observed_direct result) (Sem.observed_reads result) (Sem.observed_sides result).
Proof.
  intros [Hq [Hw Hp]] Hsaved; apply observation_replay; [exact (saved_trace Hsaved)|].
  apply guarded_reads_replay with owner; [unfold pending; rewrite Hq, Hw; tauto|].
  exact (saved_reads Hsaved).
Qed.
Lemma lookup_valuation st x v : R.semantic_lookup st x = Some v -> R.sigma_value st x = v.
Proof.
  unfold R.semantic_lookup, R.sigma_value; destruct (M.lookup (R.sigma st) x).
  - intro E; now inversion E.
  - destruct (S.mem x (R.dormant_bottom st)); intro E; inversion E; reflexivity.
Qed.
Lemma observations_unique values body first second :
  Sem.observes_at values body first -> Sem.observes_at values body second -> first = second.
Proof.
  intros [Ht Hvalues] [Hu Hother]. revert second Hu Hother Hvalues.
  induction Ht as [direct|target value next result Htail IH|
    target value next result Htail IH|target next result Htail IH];
    intros other Hu Hother Hvalues; inversion Hu; subst; cbn in Hother, Hvalues.
  - reflexivity.
  - assert (value = value0).
    { rewrite (Hvalues _ _ (or_introl eq_refl)), (Hother _ _ (or_introl eq_refl)); reflexivity. }
    subst value0.
    assert (result = result0).
    { apply IH; [assumption| |].
      - intros x v Hin; apply Hother; now right.
      - intros x v Hin; apply Hvalues; now right. }
    now subst result0.
  - assert (result = result0) by (apply IH; assumption). now subst result0.
  - assert (result = result0) by (apply IH; assumption). now subst result0.
Qed.
Lemma invariant_terminal_correct tf roots st : Sem.quiescent st ->
  invariant tf roots (Sem.terminal_config st) -> correct_final_state tf roots st.
Proof.
  intros Hquiet Hinv; destruct Hinv as [Hshape Hsummaries Hcontrib Hrequests Hseeds Hcontrol]. split.
  - intros owner Hroot; specialize (Hseeds owner Hroot).
    unfold demand in Hseeds; destruct Hseeds as [H|[H|H]]; [exact H| |contradiction].
    exfalso; eapply terminal_not_busy; eassumption.
  - intros owner Hsolved.
    destruct (Hsummaries owner Hsolved) as [Hbusy|[result Hsaved]].
    { exfalso; eapply terminal_not_busy; eassumption. }
    pose proof (saved_terminal_replay Hquiet Hsaved) as Hreplay.
    split; [eexists _, _, _; exact Hreplay|]. split.
    + intros direct reads sides Hother.
      destruct (replay_unique Hreplay Hother) as [<- [<- <-]].
      split; [exact (saved_direct Hsaved)|]. intros target value Hin.
      eapply DL.leq_trans; [eapply saved_sides; eassumption|].
      eapply DL.leq_trans; [apply contribution_le_aggregate|].
      destruct (Hcontrib target) as [Hbusy|Hbound]; [|exact Hbound].
      exfalso; eapply terminal_not_busy; eassumption.
    + intros other [Hother Hreads] target Hin.
      assert (E : result = other).
      { apply (@observations_unique (R.sigma_value st) (tf owner) result other); [|split; assumption].
        split; [exact (saved_trace Hsaved)|]. intros x v Hread.
        symmetry; apply lookup_valuation. eapply Sem.rhs_eval_reads_lookup; eassumption. }
      subst other; eapply terminal_spawn_solved; [exact Hquiet|exact Hrequests|].
      eapply saved_spawns; eassumption.
Qed.

Lemma empty_lookup x : R.semantic_lookup R.empty_state x = None.
Proof. unfold R.semantic_lookup, R.empty_state; cbn; rewrite ML.lookup_empty, SL.empty_spec; reflexivity. Qed.
Lemma initial_invariant tf roots : invariant tf roots (R.initial_config roots).
Proof.
  constructor.
  - constructor; cbn [R.initial_config R.cfg_state R.cfg_control active_owners].
    + apply RankLaws.empty_valid.
    + intros x H; unfold R.is_materialized, R.empty_state in H; cbn in H.
      rewrite ML.lookup_empty in H; discriminate.
    + intros x H; change (S.mem x S.empty = true) in H; rewrite SL.empty_spec in H; discriminate.
    + intros target owner H; unfold R.lookup_set, R.empty_state in H; cbn in H.
      rewrite ML.lookup_empty, SL.empty_spec in H; discriminate.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + intros owner H; contradiction.
    + reflexivity.
  - intros owner [value H]; change (R.semantic_lookup R.empty_state owner = Some value) in H.
    rewrite empty_lookup in H; discriminate.
  - intro target; right; change (D.leq (R.aggregate R.empty_state target) (R.sigma_value R.empty_state target) = true).
    rewrite aggregate_empty by reflexivity; apply DL.bottom_least.
  - intros target H; change (S.mem target S.empty = true) in H; rewrite SL.empty_spec in H; discriminate.
  - intros target Hin; right; right; exact Hin.
  - exact I.
Qed.

(** A history transport is the common contract of store mutations. The
    exceptional owner is the one whose evaluation replaces its old history. *)
Record history_transport before after (except : option V.t) : Prop := {
  transport_reads : forall owner target value, except <> Some owner ->
    read_guard (R.cfg_state before) owner target value ->
    read_guard (R.cfg_state after) owner target value;
  transport_sides : forall owner target, except <> Some owner ->
    D.leq (R.stored_contribution (R.cfg_state before) owner target)
      (R.stored_contribution (R.cfg_state after) owner target) = true;
  transport_values : forall owner, except <> Some owner ->
    D.leq (R.sigma_value (R.cfg_state before) owner)
      (R.sigma_value (R.cfg_state after) owner) = true;
  transport_incoming : forall owner, except <> Some owner ->
    incoming_bound before owner -> incoming_bound after owner;
  transport_spawns : forall target, spawn_accounted before target -> spawn_accounted after target;
  transport_ready : forall target, ready before target -> ready after target
}.
Lemma saved_transport tf before after except owner result : history_transport before after except ->
  except <> Some owner -> saved_observation tf before owner result -> saved_observation tf after owner result.
Proof.
  intros Ht Howner Hsaved; destruct Hsaved as [Htrace Hreads Hsides Hspawns Hdirect]; constructor.
  - exact Htrace.
  - intros target value Hin; eapply transport_reads; [exact Ht|exact Howner|exact (Hreads target value Hin)].
  - intros target value Hin; eapply DL.leq_trans; [exact (Hsides target value Hin)|eapply transport_sides; eassumption].
  - intros target Hin; eapply transport_spawns; [exact Ht|exact (Hspawns target Hin)].
  - eapply DL.leq_trans; [exact Hdirect|eapply transport_values; eassumption].
Qed.
Lemma evaluation_transport tf before after except fr body : history_transport before after except ->
  except <> Some (R.frame_owner fr) -> evaluation tf before fr body -> evaluation tf after fr body.
Proof.
  intros Ht Howner [reads [sides [spawns [Hp [Hr [Hl [Hpublish [Htargets Hspawn]]]]]]]].
  exists reads, sides, spawns; split; [exact Hp|]. split.
  - intros x v Hin; eapply transport_reads; [exact Ht|exact Howner|exact (Hr x v Hin)].
  - split; [exact Hl|]. split.
    + intros target Htarget; eapply DL.leq_trans; [exact (Hpublish target Htarget)|eapply transport_sides; eassumption].
    + split; [exact Htargets|]. intros target Hin; eapply transport_spawns; [exact Ht|exact (Hspawn target Hin)].
Qed.
Lemma continuation_transport tf before after except k : history_transport before after except ->
  (forall owner, In owner (suspended_owners k) -> except <> Some owner) ->
  continuation_valid tf before k -> continuation_valid tf after k.
Proof.
  intros Ht; induction k; cbn; intros Howners Hvalid; try exact I.
  - destruct Hvalid as [Hframe [Htarget Htail]]; split.
    + eapply evaluation_transport; [exact Ht|apply Howners; now left|exact Hframe].
    + split; [exact (transport_ready Ht Htarget)|].
      apply IHk; [intros x Hin; apply Howners; now right|exact Htail].
  - destruct Hvalid as [Hframe Htail]; split.
    + eapply evaluation_transport; [exact Ht|apply Howners; now left|exact Hframe].
    + apply IHk; [intros x Hin; apply Howners; now right|exact Htail].
  - destruct Hvalid as [Hframe Htail]; split.
    + eapply evaluation_transport; [exact Ht|apply Howners; now left|exact Hframe].
    + apply IHk; [intros x Hin; apply Howners; now right|exact Htail].
  - destruct Hvalid as [Hframe Htail]; split.
    + eapply evaluation_transport; [exact Ht|apply Howners; now left|exact Hframe].
    + apply IHk; [intros x Hin; apply Howners; now right|exact Htail].
  - destruct Hvalid as [[result [Hsaved Hbound]] Htail]; split; [exists result; split|].
    + eapply saved_transport; [exact Ht|apply Howners; now left|exact Hsaved].
    + eapply transport_incoming; [exact Ht|apply Howners; now left|exact Hbound].
    + apply IHk; [intros x Hin; apply Howners; now right|exact Htail].
Qed.
Lemma transport_unchanged before after except :
  R.sigma (R.cfg_state after) = R.sigma (R.cfg_state before) ->
  R.dormant_bottom (R.cfg_state after) = R.dormant_bottom (R.cfg_state before) ->
  R.readers (R.cfg_state after) = R.readers (R.cfg_state before) ->
  R.contributions (R.cfg_state after) = R.contributions (R.cfg_state before) ->
  (forall owner, except <> Some owner -> pending (R.cfg_state before) owner -> pending (R.cfg_state after) owner) ->
  (forall target, spawn_accounted before target -> spawn_accounted after target) ->
  (forall target, ready before target -> ready after target) ->
  (forall owner, except <> Some owner -> In owner (framed_owners (R.cfg_control after)) ->
    In owner (framed_owners (R.cfg_control before))) ->
  history_transport before after except.
Proof.
  intros Hsigma Hd Hreader Hside Hp Hspawn Hready Hframes; constructor.
  - intros owner target value Howner; apply read_guard_monotone; [now apply Hp| |].
    + unfold R.semantic_lookup; now rewrite Hsigma, Hd.
    + now rewrite Hreader.
  - intros owner target Howner; unfold R.stored_contribution; rewrite Hside; apply DL.leq_refl.
  - intros owner Howner; unfold R.sigma_value; rewrite Hsigma; apply DL.leq_refl.
  - intros owner Howner [Hpending|[Hnotframe|Hbound]].
    + left; exact (Hp owner Howner Hpending).
    + right; left; intro H; apply Hnotframe; exact (Hframes owner Howner H).
    + right; right; unfold R.aggregate, R.sigma_value in *; now rewrite Hside, Hsigma.
  - exact Hspawn.
  - exact Hready.
Qed.
Lemma fresh_evaluation tf c owner phase :
  evaluation tf c (R.fresh_frame (R.cfg_state c) owner phase) (tf owner).
Proof.
  exists [], [], []; split; [constructor|]. split.
  - intros x v H; contradiction.
  - split.
    + intros x v H; contradiction.
    + split.
      * intros target H; unfold R.fresh_frame in H; cbn in H; rewrite SL.empty_spec in H; discriminate.
      * split.
        -- intros target; unfold R.fresh_frame; cbn; rewrite SL.empty_spec; split.
           ++ discriminate.
           ++ intros [value H]; contradiction.
        -- intros target H; contradiction.
Qed.
Lemma dormant_saved tf c owner : R.pure_bottom_rhs tf owner = true ->
  exists result, saved_observation tf c owner result.
Proof.
  unfold R.pure_bottom_rhs; destruct (tf owner) as [direct| | |] eqn:Hbody; try discriminate.
  intro E; apply equivalent_true in E as [Hdirect _].
  exists {| Sem.Observation.observed_direct := direct;
    Sem.Observation.observed_reads := []; Sem.Observation.observed_sides := [];
    Sem.Observation.observed_spawns := [] |}; constructor; cbn.
  - rewrite Hbody; constructor.
  - intros x v H; contradiction.
  - intros x v H; contradiction.
  - intros x H; contradiction.
  - eapply DL.leq_trans; [exact Hdirect|apply DL.bottom_least].
Qed.
Lemma local_side_same fr target value : local_value (R.with_frame_side fr target value) target = value.
Proof. unfold local_value, R.with_frame_side; cbn; now rewrite ML.lookup_update_same. Qed.
Lemma local_side_other fr target value other : target <> other ->
  local_value (R.with_frame_side fr target value) other = local_value fr other.
Proof. intro H; unfold local_value, R.with_frame_side; cbn; now rewrite ML.lookup_update_other by congruence. Qed.
Lemma accumulated_covers_old fr target value :
  D.leq (local_value fr target) (R.accumulated_side_input fr target value) = true.
Proof.
  unfold local_value, R.accumulated_side_input; destruct (M.lookup _ _);
    auto using DL.join_upper_left, DL.bottom_least.
Qed.
Lemma accumulated_covers_new fr target value : D.leq value (R.accumulated_side_input fr target value) = true.
Proof. unfold R.accumulated_side_input; destruct (M.lookup _ _); auto using DL.join_upper_right, DL.leq_refl. Qed.
Lemma local_covers_side fr sides target value : local_covers fr sides ->
  local_covers (R.with_frame_side fr target (R.accumulated_side_input fr target value)) (sides ++ [(target,value)]).
Proof.
  intros Hlocal x v Hin; apply in_app_iff in Hin as [Hpast|Hnew].
  - destruct (V.eq_dec target x); subst.
    + rewrite local_side_same; eapply DL.leq_trans; [exact (Hlocal x v Hpast)|apply accumulated_covers_old].
    + rewrite local_side_other by assumption; exact (Hlocal x v Hpast).
  - cbn in Hnew; destruct Hnew as [E|H]; [inversion E; subst|contradiction].
    rewrite local_side_same; apply accumulated_covers_new.
Qed.
Lemma side_targets_side fr sides target input value : side_targets fr sides ->
  side_targets (R.with_frame_side fr target input) (sides ++ [(target,value)]).
Proof.
  intro Htargets; intro x; unfold R.with_frame_side; cbn; rewrite SL.add_spec; unfold side_targets in Htargets; rewrite (Htargets x); split.
  - intros [->|[v Hin]]; [exists value; apply in_app_iff; right; now left|].
    exists v; apply in_app_iff; now left.
  - intros [v Hin]; apply in_app_iff in Hin as [Hin|Hin]; [right; eauto|].
    cbn in Hin; destruct Hin as [E|H]; [inversion E; now left|contradiction].
Qed.
Lemma set_value_bound st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  D.leq direct (R.sigma_value next (R.frame_owner fr)) = true /\
  D.leq (R.aggregate next (R.frame_owner fr)) (R.sigma_value next (R.frame_owner fr)) = true.
Proof.
  unfold R.set_value; set (owner := R.frame_owner fr); set (candidate := D.join direct (R.aggregate st owner)).
  destruct (R.equivalent candidate (R.sigma_value st owner)) eqn:E.
  - intro H; inversion H; subst; apply equivalent_true in E as [Hbound _].
    split; eapply DL.leq_trans; [apply DL.join_upper_left|exact Hbound|apply DL.join_upper_right|exact Hbound].
  - destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled.
    + destruct (U.update false owner (R.frame_phase fr) (R.sigma_value st owner) candidate) as [phase value] eqn:Hupdate.
      assert (Hbound : D.leq candidate value = true).
      { pose proof (OSL.update_sound owner (R.frame_phase fr) (R.sigma_value st owner) candidate) as H.
        now rewrite Hupdate in H. }
      cbn; destruct (R.equivalent value (R.sigma_value st owner)) eqn:Hsame.
      * intro H; inversion H; subst; apply equivalent_true in Hsame as [Hv _].
        split; eapply DL.leq_trans; [apply DL.join_upper_left| |apply DL.join_upper_right|];
          eapply DL.leq_trans; eassumption.
      * intro H; inversion H; subst; unfold R.sigma_value; cbn; rewrite ML.lookup_update_same;
          split; eapply DL.leq_trans; [apply DL.join_upper_left|exact Hbound|apply DL.join_upper_right|exact Hbound].
    + cbn; rewrite E; intro H; inversion H; subst; unfold R.sigma_value; cbn; rewrite ML.lookup_update_same.
      split; unfold candidate; [apply DL.join_upper_left|].
      unfold R.aggregate; cbn; apply DL.join_upper_right.
Qed.
Lemma set_value_owner st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  R.frame_owner next_fr = R.frame_owner fr.
Proof.
  unfold R.set_value; repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    destruct (U.update _ _ _ _ _) eqn:? || idtac;
    intro H; inversion H; reflexivity.
Qed.

(** Queueing keeps an invalidated observation honest; materialization only
    supplies bottom at a previously absent store entry. *)
Lemma materialize_lookup st owner target value : R.semantic_lookup st target = Some value ->
  R.semantic_lookup (R.materialize st owner) target = Some value.
Proof.
  unfold R.materialize; destruct (M.lookup (R.sigma st) owner) eqn:Howner; [trivial|].
  destruct (V.eq_dec target owner) as [->|Hneq].
  - unfold R.semantic_lookup; rewrite Howner; destruct (S.mem owner (R.dormant_bottom st));
      intro H; [inversion H; subst|discriminate]. cbn; now rewrite ML.lookup_update_same.
  - unfold R.semantic_lookup; cbn; now rewrite ML.lookup_update_other.
Qed.
Lemma dormant_lookup st owner target value : R.semantic_lookup st target = Some value ->
  R.semantic_lookup (R.remember_dormant st owner) target = Some value.
Proof.
  unfold R.semantic_lookup, R.remember_dormant; cbn;
    destruct (M.lookup (R.sigma st) target); [trivial|].
  destruct (S.mem target (R.dormant_bottom st)) eqn:Hmem; [|discriminate].
  assert (S.mem target (S.add owner (R.dormant_bottom st)) = true) by
    (apply SL.add_spec; now right).
  now rewrite H.
Qed.
Lemma queue_pending st owner : pending (R.enqueue st owner) owner.
Proof. left; unfold R.enqueue; cbn; apply queue_insert_members; now left. Qed.
Lemma queue_preserves_pending st owner target : pending st target -> pending (R.enqueue st owner) target.
Proof.
  intros [H|H]; [left; apply queue_insert_members; now right|now right].
Qed.
Lemma queue_many_preserves_pending st owners target : pending st target -> pending (R.enqueue_all st owners) target.
Proof. intros [H|H]; [left; apply queue_many_members; now right|now right]. Qed.
Lemma flush_pending st target : pending (R.flush_deferred st) target <-> pending st target.
Proof.
  unfold pending, R.flush_deferred, R.enqueue_all; cbn; rewrite queue_many_members;
    intuition.
Qed.
Lemma flush_rank st : R.ranking (R.flush_deferred st) = R.ranking st.
Proof. reflexivity. Qed.
Lemma flush_order st : RankLaws.valid (R.ranking st) -> ranked_list st (R.deferred_wakes st) -> ranked_list st (R.queue st) ->
  sorted_queue st (R.deferred_wakes st) -> sorted_queue st (R.queue st) ->
  sorted_queue (R.flush_deferred st) (R.queue (R.flush_deferred st)).
Proof. intros Hv Hr Hq _ Horder; exact (queue_many_sorted Hr Hq Hv Horder). Qed.
Lemma ordered_distinct st owners : sorted_queue st owners -> NoDup owners.
Proof.
  intro H; induction H; constructor; [|exact IHStronglySorted].
  intro Hin; rewrite Forall_forall in H0; specialize (H0 a Hin); lia.
Qed.
Lemma stack_owner_not_suspended st owner k : sorted_queue st (owner :: suspended_owners k) ->
  ~ In owner (suspended_owners k).
Proof. intro H; apply ordered_distinct in H; now inversion H. Qed.
Lemma queue_below_absent st owner head tail : sorted_queue st (head::tail) ->
  priority st head < priority st owner -> ~ In owner (head::tail).
Proof.
  intros Horder Hlt Hin; pose proof (sorted_head_max Horder Hin); lia.
Qed.
Lemma rank_same st owner : R.rank_lt st owner owner = false.
Proof.
  unfold R.rank_lt, R.ranking_lt; destruct (R.Ranking.lookup (R.ranking st) owner);
    [apply Nat.ltb_irrefl|reflexivity].
Qed.
Lemma completed_from_evaluation tf c fr direct : evaluation tf c fr (Syntax.Ret direct) ->
  D.leq direct (R.sigma_value (R.cfg_state c) (R.frame_owner fr)) = true ->
  incoming_bound c (R.frame_owner fr) -> completed tf c fr.
Proof.
  intros [reads [sides [spawns [Hp [Hr [Hl [Hpublish [Htargets Hspawn]]]]]]]] Hd Hbound.
  exists {| Sem.Observation.observed_direct := direct;
    Sem.Observation.observed_reads := reads; Sem.Observation.observed_sides := sides;
    Sem.Observation.observed_spawns := spawns |}; split; [|exact Hbound]; constructor; cbn.
  - exact (prefix_finish Hp).
  - exact Hr.
  - intros target value Hin; eapply DL.leq_trans; [exact (Hl target value Hin)|].
    apply Hpublish; apply Htargets; now exists value.
  - exact Hspawn.
  - exact Hd.
Qed.
Definition demand_transport before after := forall target, demand before target -> demand after target.
Lemma spawn_transport before after : demand_transport before after ->
  (forall target, S.mem target (R.requested_spawns (R.cfg_state before)) = true ->
    S.mem target (R.requested_spawns (R.cfg_state after)) = true) ->
  forall target, spawn_accounted before target -> spawn_accounted after target.
Proof. intros Hdem Hrequested target [H|H]; [left; now apply Hdem|right; now apply Hrequested]. Qed.
Lemma requests_transport before after : demand_transport before after ->
  R.requested_spawns (R.cfg_state after) = R.requested_spawns (R.cfg_state before) ->
  (forall target, In target (R.pending_spawns (R.cfg_state before)) ->
    In target (R.pending_spawns (R.cfg_state after)) \/ demand after target) ->
  requests_accounted before -> requests_accounted after.
Proof.
  intros Hd Hrequested Hpending Hrequests target Hin; rewrite Hrequested in Hin.
  destruct (Hrequests target Hin) as [H|H]; [exact (Hpending target H)|right; now apply Hd].
Qed.
Lemma seeds_transport roots before after : demand_transport before after ->
  seeds_accounted roots before -> seeds_accounted roots after.
Proof. intros Hd Hseeds target Hroot; apply Hd; now apply Hseeds. Qed.
Lemma demand_same_store before after : store_view (R.cfg_state after) (R.cfg_state before) ->
  (forall owner, busy before owner -> demand after owner) ->
  (forall owner, In owner (seed_owners (R.cfg_control before)) -> demand after owner) ->
  demand_transport before after.
Proof.
  intros Hview Hbusy Hseeds target [Hsolved|[Hactive|Hseed]].
  - left; apply (proj2 (solved_view target Hview)); exact Hsolved.
  - now apply Hbusy.
  - now apply Hseeds.
Qed.
Lemma evaluation_frame tf c first second body :
  R.frame_owner first = R.frame_owner second ->
  R.frame_local_side first = R.frame_local_side second ->
  R.frame_current_targets first = R.frame_current_targets second ->
  evaluation tf c first body -> evaluation tf c second body.
Proof.
  intros Howner Hlocal Htargets [reads [sides [spawns H]]]; exists reads, sides, spawns.
  unfold reads_guarded, local_covers, locals_published, side_targets, local_value in *.
  rewrite <- Howner, <- Hlocal, <- Htargets. exact H.
Qed.
Lemma evaluation_phase tf c fr phase body : evaluation tf c fr body ->
  evaluation tf c (R.with_frame_phase fr phase) body.
Proof. apply evaluation_frame; reflexivity. Qed.
Lemma evaluation_read tf c fr minimum maximum body : evaluation tf c fr body ->
  evaluation tf c (R.with_frame_read fr minimum maximum) body.
Proof. apply evaluation_frame; reflexivity. Qed.
Lemma evaluation_get tf c fr target next value : evaluation tf c fr (Syntax.Get target next) ->
  read_guard (R.cfg_state c) (R.frame_owner fr) target value -> evaluation tf c fr (next value).
Proof.
  intros [reads [sides [spawns [Hp [Hr Hrest]]]]] Hread.
  exists (reads ++ [(target,value)]), sides, spawns; split; [now constructor|]. split.
  - intros x v Hin; apply in_app_iff in Hin as [Hin|Hin]; [exact (Hr x v Hin)|].
    cbn in Hin; destruct Hin as [E|H]; [inversion E; subst; exact Hread|contradiction].
  - exact Hrest.
Qed.
Lemma evaluation_spawn tf c fr target next : evaluation tf c fr (Syntax.Spawn target next) ->
  spawn_accounted c target -> evaluation tf c fr next.
Proof.
  intros [reads [sides [spawns [Hp [Hr [Hl [Hpub [Htargets Hspawn]]]]]]]] Htarget.
  exists reads, sides, (spawns ++ [target]); split; [now constructor|].
  split; [exact Hr|]; split; [exact Hl|]; split; [exact Hpub|]; split; [exact Htargets|].
  intros x Hin; apply in_app_iff in Hin as [H|H]; [exact (Hspawn x H)|].
  cbn in H; destruct H as [->|H]; [exact Htarget|contradiction].
Qed.
Lemma frame_owner_phase fr phase : R.frame_owner (R.with_frame_phase fr phase) = R.frame_owner fr.
Proof. reflexivity. Qed.
Lemma frame_owner_read fr minimum maximum : R.frame_owner (R.with_frame_read fr minimum maximum) = R.frame_owner fr.
Proof. reflexivity. Qed.
Lemma frame_owner_side fr target value : R.frame_owner (R.with_frame_side fr target value) = R.frame_owner fr.
Proof. reflexivity. Qed.

(** Administrative steps change the cursor but leave observation-relevant
    data alone. Keeping this contract explicit avoids repeatedly expanding
    the large state record in control-flow arguments. *)
Record logical_view before after : Prop := {
  view_sigma : R.sigma (R.cfg_state after) = R.sigma (R.cfg_state before);
  view_dormant : R.dormant_bottom (R.cfg_state after) = R.dormant_bottom (R.cfg_state before);
  view_readers : R.readers (R.cfg_state after) = R.readers (R.cfg_state before);
  view_sides : R.contributions (R.cfg_state after) = R.contributions (R.cfg_state before);
  view_ranks : R.ranking (R.cfg_state after) = R.ranking (R.cfg_state before);
  view_queue : R.queue (R.cfg_state after) = R.queue (R.cfg_state before);
  view_wakes : R.deferred_wakes (R.cfg_state after) = R.deferred_wakes (R.cfg_state before);
  view_requests : R.requested_spawns (R.cfg_state after) = R.requested_spawns (R.cfg_state before);
  view_fifo : R.pending_spawns (R.cfg_state after) = R.pending_spawns (R.cfg_state before);
  view_active : active_owners (R.cfg_control after) = active_owners (R.cfg_control before);
  view_frames : framed_owners (R.cfg_control after) = framed_owners (R.cfg_control before);
  view_seeds : seed_owners (R.cfg_control after) = seed_owners (R.cfg_control before)
}.
Lemma demand_view before after : logical_view before after -> demand_transport before after.
Proof.
  intros Hv; destruct Hv; unfold demand_transport, demand, busy, pending, solved,
    Sem.solved, R.semantic_lookup; now rewrite view_sigma0, view_dormant0,
    view_queue0, view_wakes0, view_active0, view_seeds0.
Qed.
Lemma history_view before after : logical_view before after -> history_transport before after None.
Proof.
  intro H; eapply transport_unchanged.
  - exact (view_sigma H).
  - exact (view_dormant H).
  - exact (view_readers H).
  - exact (view_sides H).
  - intros owner _; unfold pending; now rewrite (view_queue H), (view_wakes H).
  - apply spawn_transport; [now apply demand_view|].
    intros target; now rewrite (view_requests H).
  - intros target [Hs|Hb].
    + left; apply (proj2 (solved_view target (conj (view_sigma H) (view_dormant H)))); exact Hs.
    + right; unfold busy, pending in *; now rewrite (view_queue H), (view_wakes H), (view_active H).
  - intros owner _ Hmember; now rewrite (view_frames H) in Hmember.
Qed.
Lemma evaluation_view tf before after fr body : logical_view before after ->
  evaluation tf before fr body -> evaluation tf after fr body.
Proof. intro H; apply (@evaluation_transport tf before after None fr body (history_view H)); discriminate. Qed.
Lemma continuation_view tf before after k : logical_view before after ->
  continuation_valid tf before k -> continuation_valid tf after k.
Proof. intro H; apply (@continuation_transport tf before after None k (history_view H)); discriminate. Qed.
Lemma completed_view tf before after fr : logical_view before after ->
  completed tf before fr -> completed tf after fr.
Proof.
  intros H [result [Hsaved Hbound]]; exists result; split.
  - eapply (@saved_transport tf before after None _ _); [exact (history_view H)|discriminate|exact Hsaved].
  - eapply (@transport_incoming before after None); [exact (history_view H)|discriminate|exact Hbound].
Qed.
Lemma invariant_view tf roots before after : logical_view before after ->
  (wakes_finished before -> wakes_finished after) -> control_valid tf after ->
  invariant tf roots before -> invariant tf roots after.
Proof.
  intros Hview Hwakes Hcontrol Hinv; destruct Hinv as [Hshape Hsummaries Hbounds Hrequests Hseeds _].
  constructor.
  - destruct Hshape; constructor.
    + now rewrite (view_ranks Hview).
    + intros x H; unfold ranked; rewrite (view_ranks Hview); apply shape_materialized0.
      unfold R.is_materialized in *; now rewrite (view_sigma Hview) in H.
    + intros x H; apply shape_dormant0; now rewrite (view_dormant Hview) in H.
    + intros target owner H; unfold ranked; rewrite (view_ranks Hview); apply shape_readers0 with target.
      now rewrite (view_readers Hview) in H.
    + unfold ranked_list, ranked; now rewrite (view_queue Hview), (view_ranks Hview).
    + unfold ranked_list, ranked; now rewrite (view_wakes Hview), (view_ranks Hview).
    + unfold sorted_queue, priority; now rewrite (view_queue Hview), (view_ranks Hview).
    + unfold sorted_queue, priority; now rewrite (view_wakes Hview), (view_ranks Hview).
    + unfold ranked_list, ranked; now rewrite (view_active Hview), (view_ranks Hview).
    + unfold sorted_queue, priority; now rewrite (view_active Hview), (view_ranks Hview).
    + intros owner H; apply (proj2 (solved_view owner (conj (view_sigma Hview) (view_dormant Hview))));
      apply shape_live_frames0; now rewrite (view_frames Hview) in H.
    + now apply Hwakes.
  - intros owner Hsolved; assert (Hold : solved (R.cfg_state before) owner).
    { apply (proj1 (solved_view owner (conj (view_sigma Hview) (view_dormant Hview)))); exact Hsolved. }
    destruct (Hsummaries owner Hold) as [Hbusy|[result Hsaved]].
    + left; unfold busy, pending in *; now rewrite (view_queue Hview), (view_wakes Hview), (view_active Hview).
    + right; exists result; eapply (@saved_transport tf before after None owner result); [exact (history_view Hview)|discriminate|exact Hsaved].
  - intros target; destruct (Hbounds target) as [Hbusy|Hbound].
    + left; unfold busy, pending in *; now rewrite (view_queue Hview), (view_wakes Hview), (view_active Hview).
    + right; unfold R.aggregate, R.sigma_value; now rewrite (view_sides Hview), (view_sigma Hview).
  - eapply (@requests_transport before after); [exact (demand_view Hview)|exact (view_requests Hview)| |exact Hrequests].
    intros target H; left; now rewrite (view_fifo Hview).
  - eapply (@seeds_transport roots before after); [exact (demand_view Hview)|exact Hseeds].
  - exact Hcontrol.
Qed.
Definition configuration st ctrl : R.config := {| R.cfg_state := st; R.cfg_control := ctrl |}.
Lemma control_view st first second : active_owners second = active_owners first ->
  seed_owners second = seed_owners first -> framed_owners second = framed_owners first ->
  logical_view (configuration st first) (configuration st second).
Proof. intros Ha Hs Hf; constructor; cbn; reflexivity || assumption. Qed.
Ltac use_invariant_view H :=
  lazymatch type of H with
  | invariant ?tf ?roots ?before => eapply (@invariant_view tf roots before _)
  end.
Ltac transport_cursor H :=
  let Hcursor := fresh "Hcursor" in
  pose proof (inv_control H) as Hcursor;
  cbn [control_valid configuration R.cfg_control] in Hcursor |- *;
  destruct Hcursor as [Hframe Htail]; split;
  [first [eapply evaluation_view; [|exact Hframe] |
          eapply completed_view; [|exact Hframe]] |
   eapply continuation_view; [|exact Htail]];
  apply control_view; reflexivity.
Lemma ret_preserves tf roots st fr direct k :
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Ret direct) k)) ->
  invariant tf roots (configuration st (R.RunDead fr direct
    (if Features.eliminate_dead_sides then S.elements (R.frame_previous_targets fr) else []) k)).
Proof.
  intro H; use_invariant_view H; [apply control_view; reflexivity|intros; exact I| |exact H].
  transport_cursor H.
Qed.
Lemma dead_skip_preserves tf roots st fr direct pending k :
  invariant tf roots (configuration st (R.RunDead fr direct pending k)) ->
  forall rest, invariant tf roots (configuration st (R.RunDead fr direct rest k)).
Proof.
  intros H rest; use_invariant_view H; [apply control_view; reflexivity|intros; exact I| |exact H].
  transport_cursor H.
Qed.
Lemma finish_dead_preserves tf roots st fr direct k :
  invariant tf roots (configuration st (R.RunDead fr direct [] k)) ->
  invariant tf roots (configuration (R.publish_targets st fr) (R.RunCommit fr direct k)).
Proof.
  intro H; assert (Hv : logical_view (configuration st (R.RunDead fr direct [] k))
    (configuration (R.publish_targets st fr) (R.RunCommit fr direct k))) by (constructor; reflexivity).
  use_invariant_view H; [exact Hv|intros; exact I| |exact H].
  destruct (inv_control H) as [He Hk]; split.
  - eapply evaluation_view; eassumption.
  - eapply continuation_view; eassumption.
Qed.
Lemma return_loop_preserves tf roots st : invariant tf roots (configuration st (R.Return R.KLoop)) ->
  invariant tf roots (configuration st R.RunLoop).
Proof.
  intro H; use_invariant_view H; [apply control_view; reflexivity| |exact I|exact H].
  unfold wakes_finished, configuration; cbn; trivial.
Qed.
Lemma return_seeds_preserves tf roots st remaining :
  invariant tf roots (configuration st (R.Return (R.KSeedLoop remaining))) ->
  invariant tf roots (configuration st (R.RunSeedLoop remaining)).
Proof.
  intro H; use_invariant_view H; [apply control_view; reflexivity| |exact I|exact H].
  unfold wakes_finished, configuration; cbn; trivial.
Qed.
Lemma return_side_preserves tf roots st fr next k :
  invariant tf roots (configuration st (R.Return (R.KAfterSide fr next k))) ->
  invariant tf roots (configuration st (R.RunRhs fr next k)).
Proof.
  intro H; use_invariant_view H; [apply control_view; reflexivity|intros; exact I| |exact H].
  transport_cursor H.
Qed.
Lemma return_spawn_preserves tf roots st fr next k :
  invariant tf roots (configuration st (R.Return (R.KAfterSpawn fr next k))) ->
  invariant tf roots (configuration st (R.RunRhs fr next k)).
Proof.
  intro H; use_invariant_view H; [apply control_view; reflexivity|intros; exact I| |exact H].
  transport_cursor H.
Qed.
Lemma return_dead_preserves tf roots st fr direct remaining k :
  invariant tf roots (configuration st (R.Return (R.KDead fr direct remaining k))) ->
  invariant tf roots (configuration st (R.RunDead fr direct remaining k)).
Proof.
  intro H; use_invariant_view H; [apply control_view; reflexivity|intros; exact I| |exact H].
  transport_cursor H.
Qed.
Lemma return_drain_preserves tf roots st fr k :
  invariant tf roots (configuration st (R.Return (R.KDrain fr k))) ->
  invariant tf roots (configuration st (R.RunDrain fr k)).
Proof.
  intro H; use_invariant_view H; [apply control_view; reflexivity| | |exact H].
  - unfold wakes_finished, configuration; cbn; trivial.
  - transport_cursor H.
Qed.

Lemma pop_start_preserves tf roots st ctrl owner tail k :
  R.queue st = owner :: tail -> active_owners ctrl = [] -> suspended_owners k = [] ->
  seed_owners ctrl = suspended_seeds k -> continuation_valid tf (configuration st ctrl) k ->
  invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (R.with_queue st tail) (R.StartEpisode owner k)).
Proof.
  intros Hqueue Hactive Hstack Hseeds Hkont Hinv.
  set (before := configuration st ctrl) in *.
  set (after := configuration (R.with_queue st tail) (R.StartEpisode owner k)).
  assert (Hbusy : forall x, busy before x -> busy after x).
  { intros x; unfold before, after, configuration, busy, pending; cbn; rewrite Hqueue, Hactive, Hstack; cbn.
    intros [[H|H]|H]; [destruct H as [->|H]; [right; now left|left; now left]|left; now right|contradiction]. }
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [split; reflexivity| |].
    - intros x H; right; left; now apply Hbusy.
    - intros x H; right; right; unfold before, after, configuration in *; cbn in *; now rewrite <- Hseeds. }
  assert (Hhistory : history_transport before after (Some owner)).
  { apply transport_unchanged; try reflexivity.
    - intros x Hneq; unfold before, after, configuration, pending; cbn; rewrite Hqueue.
      intros [[H|H]|H]; [subst; contradiction|left; exact H|right; exact H].
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x [Hs|Hb]; [now left|right; now apply Hbusy].
    - intros x _ H; change (In x (suspended_owners k)) in H; rewrite Hstack in H; contradiction. }
  destruct Hinv as [Hshape Hsummaries Hbounds Hrequests Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hlive Hd Hreader Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor.
    + exact Hv.
    + exact Hlive.
    + exact Hd.
    + exact Hreader.
    + change (ranked_list st tail); change (ranked_list st (R.queue st)) in Hqr.
      rewrite Hqueue in Hqr; now inversion Hqr.
    + exact Hwr.
    + change (sorted_queue st tail); change (sorted_queue st (R.queue st)) in Hqo.
      rewrite Hqueue in Hqo; now inversion Hqo.
    + exact Hwo.
    + change (ranked_list st (owner :: suspended_owners k)); rewrite Hstack.
      change (ranked_list st (R.queue st)) in Hqr; rewrite Hqueue in Hqr; inversion Hqr; subst.
      constructor; [assumption|constructor].
    + change (sorted_queue st (owner :: suspended_owners k)); rewrite Hstack.
      constructor; constructor.
    + intros x H; change (In x (suspended_owners k)) in H; rewrite Hstack in H; contradiction.
    + exact I.
  - intros x Hsolved; destruct (V.eq_dec x owner) as [->|Hneq].
    + left; right; unfold after, configuration; cbn; now left.
    + destruct (Hsummaries x Hsolved) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
      right; exists result; eapply saved_transport; [exact Hhistory|congruence|exact Hsaved].
  - intros x; destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|right; exact Hb].
  - eapply (@requests_transport before after); [exact Hdem|reflexivity| |exact Hrequests].
    intros x H; now left.
  - exact (seeds_transport Hdem Hroots).
  - unfold after, configuration, control_valid; cbn.
    eapply (@continuation_transport tf before after (Some owner) k); [exact Hhistory| |exact Hkont].
    intros x H; rewrite Hstack in H; contradiction.
Qed.
Lemma loop_pop_preserves tf roots st owner tail : R.queue st = owner :: tail ->
  invariant tf roots (configuration st R.RunLoop) ->
  invariant tf roots (configuration (R.with_queue st tail) (R.StartEpisode owner R.KLoop)).
Proof. intros Hqueue Hinv; eapply (@pop_start_preserves tf roots st R.RunLoop owner tail R.KLoop);
  try reflexivity; eauto; exact I. Qed.
Lemma seed_loop_pop_preserves tf roots st remaining owner tail : R.queue st = owner :: tail ->
  invariant tf roots (configuration st (R.RunSeedLoop remaining)) ->
  invariant tf roots (configuration (R.with_queue st tail) (R.StartEpisode owner (R.KSeedLoop remaining))).
Proof. intros Hqueue Hinv; eapply (@pop_start_preserves tf roots st (R.RunSeedLoop remaining) owner tail (R.KSeedLoop remaining));
  try reflexivity; eauto; exact I. Qed.
Lemma lookup_after_materialize st owner x : x <> owner ->
  R.semantic_lookup (R.materialize st owner) x = R.semantic_lookup st x.
Proof.
  intro Hneq; unfold R.materialize; destruct (M.lookup (R.sigma st) owner); [reflexivity|].
  unfold R.semantic_lookup; cbn; now rewrite ML.lookup_update_other.
Qed.
Lemma start_episode_preserves tf roots st owner k :
  invariant tf roots (configuration st (R.StartEpisode owner k)) ->
  invariant tf roots (configuration (R.clear_side_dirty (R.materialize st owner) owner)
    (R.RunRhs (R.fresh_frame (R.clear_side_dirty (R.materialize st owner) owner)
      owner (U.initial_phase false owner)) (tf owner) k)).
Proof.
  intro Hinv; set (prepared := R.clear_side_dirty (R.materialize st owner) owner).
  set (before := configuration st (R.StartEpisode owner k)) in *.
  set (after := configuration prepared (R.RunRhs (R.fresh_frame prepared owner (U.initial_phase false owner)) (tf owner) k)).
  assert (Hrank : R.ranking prepared = R.ranking st).
  { unfold prepared, R.materialize; destruct (M.lookup (R.sigma st) owner); reflexivity. }
  assert (Hqueue : R.queue prepared = R.queue st).
  { unfold prepared, R.materialize; destruct (M.lookup (R.sigma st) owner); reflexivity. }
  assert (Hwake : R.deferred_wakes prepared = R.deferred_wakes st).
  { unfold prepared, R.materialize; destruct (M.lookup (R.sigma st) owner); reflexivity. }
  assert (Hreader : R.readers prepared = R.readers st).
  { unfold prepared, R.materialize; destruct (M.lookup (R.sigma st) owner); reflexivity. }
  assert (Hcontrib : R.contributions prepared = R.contributions st).
  { unfold prepared, R.materialize; destruct (M.lookup (R.sigma st) owner); reflexivity. }
  assert (Hdormant : R.dormant_bottom prepared = R.dormant_bottom st).
  { unfold prepared, R.materialize; destruct (M.lookup (R.sigma st) owner); reflexivity. }
  assert (Hrequests : R.requested_spawns prepared = R.requested_spawns st).
  { unfold prepared, R.materialize; destruct (M.lookup (R.sigma st) owner); reflexivity. }
  assert (Hfifo : R.pending_spawns prepared = R.pending_spawns st).
  { unfold prepared, R.materialize; destruct (M.lookup (R.sigma st) owner); reflexivity. }
  assert (Hvalue : forall x, R.sigma_value prepared x = R.sigma_value st x).
  { intro x; unfold prepared; change (R.sigma_value (R.materialize st owner) x = R.sigma_value st x).
    apply materialize_valuation. }
  assert (Hlookup : forall x value, R.semantic_lookup st x = Some value -> R.semantic_lookup prepared x = Some value).
  { intros x value H; change (R.semantic_lookup (R.materialize st owner) x = Some value); now apply materialize_lookup. }
  assert (Hlookup_other : forall x, x <> owner -> R.semantic_lookup prepared x = R.semantic_lookup st x).
  { intros x H; change (R.semantic_lookup (R.materialize st owner) x = R.semantic_lookup st x); now apply lookup_after_materialize. }
  assert (Hsolves : forall x, solved st x -> solved prepared x).
  { intros x H; change (solved (R.materialize st owner) x); now apply materialize_preserves. }
  assert (Hlive_other : forall x, x <> owner -> R.is_materialized prepared x = true -> R.is_materialized st x = true).
  { intros x Hneq; unfold prepared, R.materialize, R.is_materialized; destruct (M.lookup (R.sigma st) owner); [trivial|].
    cbn; now rewrite ML.lookup_update_other. }
  assert (Howner_live : solved prepared owner).
  { change (solved (R.materialize st owner) owner); apply materialize_solves. }
  clearbody prepared.
  assert (Hbusy : forall x, busy before x -> busy after x).
  { intro x; change (pending st x \/ In x (owner :: suspended_owners k) ->
      pending prepared x \/ In x (owner :: suspended_owners k)).
    unfold pending; now rewrite Hqueue, Hwake. }
  assert (Hdem : demand_transport before after).
  { intros x [H|[H|H]].
    - left; now apply Hsolves.
    - right; left; now apply Hbusy.
    - right; right; exact H. }
  assert (Hhistory : history_transport before after (Some owner)).
  { constructor.
    - intros x target value _; unfold read_guard; unfold before, after, configuration; cbn.
      intros [Hp|[Hl Hr]].
      + left; unfold pending in *; now rewrite Hqueue, Hwake.
      + right; split.
        * now apply Hlookup.
        * now rewrite Hreader.
    - intros x target _; unfold before, after, configuration; cbn; unfold R.stored_contribution;
        rewrite Hcontrib; apply DL.leq_refl.
    - intros x _; unfold before, after, configuration; cbn; rewrite Hvalue; apply DL.leq_refl.
    - intros x Hneq [Hp|[Hnot|Hb]].
      + left; unfold before, after, configuration, pending in *; cbn in *; now rewrite Hqueue, Hwake.
      + right; left; intro H; change (In x (owner :: suspended_owners k)) in H; destruct H as [E|H];
          [subst x; contradiction|apply Hnot; exact H].
      + right; right; unfold before, after, configuration, R.aggregate in *; cbn in *; now rewrite Hcontrib, Hvalue.
    - apply spawn_transport; [exact Hdem|intros x; unfold before, after, configuration; cbn; now rewrite Hrequests].
    - intros x [Hs|Hb]; [left; now apply Hsolves|right; now apply Hbusy]. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor.
    + unfold after, configuration; cbn; now rewrite Hrank.
    + intros x H; unfold after, configuration in H |- *; cbn in H |- *; unfold ranked; rewrite Hrank.
      destruct (V.eq_dec x owner) as [->|Hneq].
      * change (ranked_list st (owner :: suspended_owners k)) in Har; now inversion Har.
      * apply Hlive; exact (Hlive_other x Hneq H).
    + intros x H; apply Hd; unfold after, configuration in H; cbn in H; now rewrite Hdormant in H.
    + intros target x H; unfold after, configuration in H |- *; cbn in H |- *; unfold ranked; rewrite Hrank.
      apply Hr with target; now rewrite Hreader in H.
    + unfold after, configuration, ranked_list, ranked; cbn; now rewrite Hqueue, Hrank.
    + unfold after, configuration, ranked_list, ranked; cbn; now rewrite Hwake, Hrank.
    + unfold after, configuration, sorted_queue, priority; cbn; now rewrite Hqueue, Hrank.
    + unfold after, configuration, sorted_queue, priority; cbn; now rewrite Hwake, Hrank.
    + unfold after, before, configuration, ranked_list, ranked, active_owners in *; cbn in *; now rewrite Hrank.
    + unfold after, before, configuration, sorted_queue, priority, active_owners in *; cbn in *; now rewrite Hrank.
    + intros x H; change (In x (owner :: suspended_owners k)) in H.
      destruct H as [->|H]; [exact Howner_live|apply Hsolves; exact (Hframes x H)].
    + exact I.
  - intros x Hsolved; destruct (V.eq_dec x owner) as [->|Hneq].
    + left; right; unfold after, configuration; cbn; now left.
    + assert (Hold : solved st x).
      { destruct Hsolved as [v H]; exists v; change (R.semantic_lookup prepared x = Some v) in H.
        now rewrite Hlookup_other in H. }
      destruct (Hsummary x Hold) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
      right; exists result; eapply (@saved_transport tf before after (Some owner) x result);
        [exact Hhistory|congruence|exact Hsaved].
  - intros x; destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|right].
    unfold after, configuration; cbn; unfold R.aggregate; rewrite Hcontrib, Hvalue; exact Hb.
  - eapply (@requests_transport before after); [exact Hdem|exact Hrequests| |exact Hreq].
    intros x H; left; unfold after, configuration; cbn; now rewrite Hfifo.
  - exact (seeds_transport Hdem Hroots).
  - unfold after, configuration, control_valid; cbn; split; [apply fresh_evaluation|].
    eapply (@continuation_transport tf before after (Some owner) k); [exact Hhistory| |exact Hcontrol].
    intros x Hin E; pose proof (@stack_owner_not_suspended st owner k (shape_stack_order Hshape)) as Hnot;
    inversion E; subst; now apply Hnot.
Qed.

(** Publication has one observable write, invalidates exactly the registered
    readers, and optionally adds the controlled owner to the same work queue. *)
Definition commit_publication st owner value :=
  let written := R.with_sigma st (M.update (R.sigma st) owner value) in
  let invalidated := S.elements (R.lookup_set (R.readers st) owner) in
  let notified := R.enqueue_all written invalidated in
  let cleared := R.with_readers notified (M.update (R.readers st) owner S.empty) in
  R.with_queue cleared
    (if S.mem owner (R.controlled st) && Features.recompute_controlled
     then R.queue_insert (R.ranking st) owner (R.queue cleared) else R.queue cleared).
Lemma publication_value st owner value : R.sigma_value (commit_publication st owner value) owner = value.
Proof. unfold commit_publication, R.sigma_value; cbn; now rewrite ML.lookup_update_same. Qed.
Lemma publication_other st owner value target : target <> owner ->
  R.semantic_lookup (commit_publication st owner value) target = R.semantic_lookup st target.
Proof. intro H; unfold commit_publication, R.semantic_lookup; cbn; now rewrite ML.lookup_update_other. Qed.
Lemma publication_members st owner value target :
  In target (R.queue (commit_publication st owner value)) <->
  In target (R.queue st) \/ S.mem target (R.lookup_set (R.readers st) owner) = true \/
  (target = owner /\ S.mem owner (R.controlled st) = true /\ Features.recompute_controlled = true).
Proof.
  unfold commit_publication; cbn; destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled;
    destruct Features.recompute_controlled eqn:Hrecompute; cbn;
    repeat rewrite queue_insert_members; rewrite queue_many_members; rewrite <- SL.mem_spec; intuition congruence.
Qed.
Lemma publication_pending st owner value target : pending st target -> pending (commit_publication st owner value) target.
Proof.
  intros [H|H]; [left; apply publication_members; now left|right; exact H].
Qed.
Lemma publication_read_guard st owner value reader target observed : read_guard st reader target observed ->
  read_guard (commit_publication st owner value) reader target observed.
Proof.
  intros [Hp|[Hl Hr]]; [left; now apply publication_pending|].
  destruct (V.eq_dec target owner) as [->|Hneq].
  - left; left; apply publication_members; right; now left.
  - right; split; [now rewrite publication_other|].
    unfold commit_publication, R.lookup_set; cbn; now rewrite ML.lookup_update_other.
Qed.
Lemma publication_recomputes st owner value : Features.recompute_controlled = true ->
  S.mem owner (R.controlled st) = true -> In owner (R.queue (commit_publication st owner value)).
Proof. intros Hrecompute Hcontrolled; apply publication_members; right; right; auto. Qed.
Lemma set_value_cases st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  let owner := R.frame_owner fr in
  let old := R.sigma_value st owner in
  let input := D.join direct (R.aggregate st owner) in
  (R.equivalent input old = true /\ next = st /\ next_fr = fr) \/
  (R.equivalent input old = false /\
   let result := if S.mem owner (R.controlled st)
     then U.update false owner (R.frame_phase fr) old input else (R.frame_phase fr,input) in
   next_fr = R.with_frame_phase fr (fst result) /\
   ((R.equivalent (snd result) old = true /\ next = st) \/
    (R.equivalent (snd result) old = false /\ next = commit_publication st owner (snd result)))).
Proof.
  unfold R.set_value; cbn zeta; destruct (R.equivalent (D.join direct (R.aggregate st (R.frame_owner fr)))
    (R.sigma_value st (R.frame_owner fr))) eqn:Hcandidate.
  - intro H; inversion H; subst; left; auto.
  - destruct (S.mem (R.frame_owner fr) (R.controlled st)) eqn:Hcontrolled.
    + destruct (U.update false (R.frame_owner fr) (R.frame_phase fr)
        (R.sigma_value st (R.frame_owner fr)) (D.join direct (R.aggregate st (R.frame_owner fr))))
        as [phase value] eqn:Hupdate; cbn;
        destruct (R.equivalent value (R.sigma_value st (R.frame_owner fr))) eqn:Hvalue;
        intro H; inversion H; subst.
      * right; split; [reflexivity|]; split; [reflexivity|]. left; auto.
      * right; split; [reflexivity|]; split; [reflexivity|].
        right; split; [reflexivity|]; unfold commit_publication; rewrite Hcontrolled; reflexivity.
    + cbn; rewrite Hcandidate; intro H; inversion H; subst; right; split; [reflexivity|]; split; [reflexivity|].
      right; split; [reflexivity|]; unfold commit_publication; rewrite Hcontrolled; reflexivity.
Qed.
Lemma set_value_read_guard st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  forall reader target observed, read_guard st reader target observed -> read_guard next reader target observed.
Proof.
  intro H; apply set_value_cases in H as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]];
    auto using publication_read_guard.
Qed.
Lemma set_value_other_lookup st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  forall target, target <> R.frame_owner fr -> R.semantic_lookup next target = R.semantic_lookup st target.
Proof.
  intro H; apply set_value_cases in H as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]];
    auto using publication_other.
Qed.
Lemma set_value_pending st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  forall target, pending st target -> pending next target.
Proof.
  intro H; apply set_value_cases in H as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]];
    auto using publication_pending.
Qed.
Lemma changed_controlled_requeues st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  S.mem (R.frame_owner fr) (R.controlled st) = true -> Features.recompute_controlled = true ->
  ~ eqv (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) ->
  In (R.frame_owner fr) (R.queue next).
Proof.
  intros H Hcontrolled Hrecompute Hchange; apply set_value_cases in H as
    [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; try (exfalso; apply Hchange; apply eqv_refl).
  now apply publication_recomputes.
Qed.
Lemma set_value_metadata st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  R.ranking next = R.ranking st /\ R.contributions next = R.contributions st /\
  R.dormant_bottom next = R.dormant_bottom st /\ R.deferred_wakes next = R.deferred_wakes st /\
  R.pending_spawns next = R.pending_spawns st /\ R.requested_spawns next = R.requested_spawns st.
Proof.
  intro H; apply set_value_cases in H as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]];
    repeat split; reflexivity.
Qed.
Lemma set_value_solved st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  forall owner, solved st owner -> solved next owner.
Proof.
  intro H; apply set_value_cases in H as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; try trivial.
  intros x Hsolved; change (solved (R.with_sigma st (M.update (R.sigma st) (R.frame_owner fr)
    (snd (if S.mem (R.frame_owner fr) (R.controlled st)
      then U.update false (R.frame_owner fr) (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
        (D.join direct (R.aggregate st (R.frame_owner fr))) else (R.frame_phase fr,D.join direct (R.aggregate st (R.frame_owner fr))))))) x).
  now apply sigma_write_preserves.
Qed.

Lemma register_reset_view st source target scope phase ctrl :
  logical_view (configuration st ctrl) (configuration (R.register_reset st source target scope phase) ctrl).
Proof. constructor; reflexivity. Qed.
Lemma reset_cells_view st scope ctrl :
  logical_view (configuration st ctrl) (configuration (R.reset_registered_cells st scope) ctrl).
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; constructor; reflexivity. Qed.
Lemma side_write_published st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  D.leq input (R.stored_contribution next (R.frame_owner fr) target) = true.
Proof.
  unfold R.write_side_contribution; intro H; inversion H; subst.
  unfold R.stored_contribution; cbn; unfold R.update_map, R.lookup_map; rewrite ML.lookup_update_same, ML.lookup_update_same.
  unfold R.side_update; apply SSL.update_sound.
Qed.
Lemma side_write_other_source st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  forall owner observed, owner <> R.frame_owner fr ->
  R.stored_contribution next owner observed = R.stored_contribution st owner observed.
Proof.
  unfold R.write_side_contribution; intro H; inversion H; subst.
  intros owner observed Hneq; unfold R.stored_contribution; cbn.
  destruct (V.eq_dec observed target) as [->|Hother].
  - unfold R.update_map, R.lookup_map; rewrite ML.lookup_update_same, ML.lookup_update_other by congruence; unfold R.promote_side_target;
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
  - unfold R.update_map, R.lookup_map; rewrite ML.lookup_update_other by congruence; unfold R.promote_side_target;
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
Qed.
Lemma side_write_other_target st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  forall observed, observed <> target ->
  R.lookup_map (R.contributions next) observed = R.lookup_map (R.contributions st) observed.
Proof.
  unfold R.write_side_contribution; intro H; inversion H; subst; intros observed Hneq.
  unfold R.lookup_map; cbn; unfold R.update_map; rewrite ML.lookup_update_other by congruence.
  unfold R.promote_side_target; destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
Qed.
Lemma side_write_other_aggregate st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  forall observed, observed <> target -> R.aggregate next observed = R.aggregate st observed.
Proof. intros H observed Hneq; unfold R.aggregate; now rewrite (side_write_other_target H Hneq). Qed.
Lemma side_write_unchanged_aggregate st fr target input next :
  R.write_side_contribution st fr target input = (next,false) ->
  eqv (R.aggregate next target) (R.aggregate st target).
Proof.
  unfold R.write_side_contribution; intro H; inversion H; subst; clear H.
  apply equivalent_true; unfold R.aggregate_changed in H2.
  apply negb_false_iff in H2; unfold R.promote_side_target in H2 |- *;
    destruct (R.rank_lt st target (R.frame_owner fr)) eqn:Hrank; exact H2.
Qed.
Lemma side_write_metadata st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  R.sigma next = R.sigma st /\ R.ranking next = R.ranking st /\
  R.readers next = R.readers st /\ R.dormant_bottom next = R.dormant_bottom st /\
  R.queue next = R.queue st /\ R.deferred_wakes next = R.deferred_wakes st /\
  R.pending_spawns next = R.pending_spawns st /\ R.requested_spawns next = R.requested_spawns st.
Proof.
  unfold R.write_side_contribution; intro H; inversion H; subst.
  unfold R.promote_side_target; destruct (R.rank_lt st target (R.frame_owner fr)); repeat split; reflexivity.
Qed.
Lemma side_write_local_publish st fr target raw next changed :
  locals_published st fr ->
  R.write_side_contribution st (R.with_frame_side fr target (R.accumulated_side_input fr target raw))
    target (R.accumulated_side_input fr target raw) = (next,changed) ->
  locals_published next (R.with_frame_side fr target (R.accumulated_side_input fr target raw)).
Proof.
  intros Hlocals Hwrite observed Hmember; unfold R.with_frame_side in Hmember; cbn in Hmember.
  apply SL.add_spec in Hmember as [->|Hmember].
  - rewrite local_side_same; exact (side_write_published Hwrite).
  - destruct (V.eq_dec observed target) as [->|Hneq]; [rewrite local_side_same; exact (side_write_published Hwrite)|].
    rewrite local_side_other by congruence; unfold R.stored_contribution.
    rewrite (side_write_other_target Hwrite Hneq); exact (Hlocals observed Hmember).
Qed.
Lemma observes_exists values body : exists result, Sem.observes_at values body result.
Proof.
  induction body as [direct|target next IH|target value next [result [Hobs Hreads]]|target next [result [Hobs Hreads]]].
  - exists {| Sem.Observation.observed_direct := direct; Sem.Observation.observed_reads := [];
      Sem.Observation.observed_sides := []; Sem.Observation.observed_spawns := [] |}; split;
      [constructor|intros x v H; contradiction].
  - destruct (IH (values target)) as [result [Hobs Hreads]].
    exists {| Sem.Observation.observed_direct := Sem.observed_direct result;
      Sem.Observation.observed_reads := (target,values target) :: Sem.observed_reads result;
      Sem.Observation.observed_sides := Sem.observed_sides result;
      Sem.Observation.observed_spawns := Sem.observed_spawns result |}; split; [now constructor|].
    intros x v [E|H]; [inversion E; subst; reflexivity|exact (Hreads x v H)].
  - exists {| Sem.Observation.observed_direct := Sem.observed_direct result;
      Sem.Observation.observed_reads := Sem.observed_reads result;
      Sem.Observation.observed_sides := (target,value) :: Sem.observed_sides result;
      Sem.Observation.observed_spawns := Sem.observed_spawns result |}; split; [now constructor|exact Hreads].
  - exists {| Sem.Observation.observed_direct := Sem.observed_direct result;
      Sem.Observation.observed_reads := Sem.observed_reads result;
      Sem.Observation.observed_sides := Sem.observed_sides result;
      Sem.Observation.observed_spawns := target :: Sem.observed_spawns result |}; split; [now constructor|exact Hreads].
Qed.
Lemma prefix_pure root body reads sides spawns :
  (forall result, Sem.rhs_observes root result -> Sem.observed_sides result = []) ->
  prefix root body reads sides spawns -> sides = [] /\
  (forall result, Sem.rhs_observes body result -> Sem.observed_sides result = []).
Proof.
  intros Hpure Hprefix; destruct (observes_exists (fun _ => D.bottom) body) as [result [Hobs _]].
  pose proof (Hpure _ (prefix_observation Hprefix Hobs)) as Heq.
  change (sides ++ Sem.observed_sides result = []) in Heq.
  apply app_eq_nil in Heq as [Hs _]; split; [exact Hs|].
  intros tail Htail; pose proof (Hpure _ (prefix_observation Hprefix Htail)) as H.
  change (sides ++ Sem.observed_sides tail = []) in H; now apply app_eq_nil in H as [_ H].
Qed.
Lemma pure_side_impossible body target value tail :
  (forall result, Sem.rhs_observes body result -> Sem.observed_sides result = []) ->
  body = Syntax.Side target value tail -> False.
Proof.
  intros Hpure ->; destruct (observes_exists (fun _ => D.bottom) tail) as [result [Hobs _]].
  specialize (Hpure _ (Sem.ObserveSide target value Hobs)); discriminate.
Qed.

Lemma control_transport tf before after : R.cfg_control after = R.cfg_control before ->
  history_transport before after None -> control_valid tf before -> control_valid tf after.
Proof.
  intros Hctrl Hhistory Hvalid; unfold control_valid in Hvalid |- *; rewrite Hctrl.
  destruct (R.cfg_control before); try exact I.
  all: try (eapply (@continuation_transport tf before after None); [exact Hhistory|discriminate|exact Hvalid]).
  all: destruct Hvalid as [Hframe Htail]; split.
  all: try (eapply (@continuation_transport tf before after None); [exact Hhistory|discriminate|exact Htail]).
  all: try (eapply (@evaluation_transport tf before after None); [exact Hhistory|discriminate|exact Hframe]).
  destruct Hframe as [result [Hsaved Hbound]]; exists result; split.
  - eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - eapply (@transport_incoming before after None); [exact Hhistory|discriminate|exact Hbound].
Qed.
Lemma observe_preserves tf roots st ctrl target : invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (R.observe st target) ctrl).
Proof.
  intro Hinv; set (before := configuration st ctrl) in *; set (after := configuration (R.observe st target) ctrl).
  assert (Hext : rank_extension st (R.observe st target)) by apply observe_extends.
  assert (Hvalid : RankLaws.valid (R.ranking (R.observe st target)))
    by (apply rank_valid_observe; exact (shape_ranks (inv_shape Hinv))).
  unfold R.observe in after, Hext, Hvalid.
  destruct (R.Ranking.observe (R.ranking st) target) as [order rank] eqn:Hobserve.
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [split; reflexivity|intros x H; right; now left|intros x H; right; now right]. }
  assert (Hhistory : history_transport before after None).
  { apply transport_unchanged; try reflexivity.
    - intros x _ H; exact H.
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x H; exact H.
    - intros x _ H; exact H. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor.
    + exact Hvalid.
    + intros x H; eapply ranked_extension; [exact Hext|now apply Hlive].
    + exact Hd.
    + intros x owner H; eapply ranked_extension; [exact Hext|exact (Hr x owner H)].
    + exact (ranked_list_extension Hext Hqr).
    + exact (ranked_list_extension Hext Hwr).
    + exact (sorted_queue_extension Hext Hqr Hqo).
    + exact (sorted_queue_extension Hext Hwr Hwo).
    + exact (ranked_list_extension Hext Har).
    + exact (sorted_queue_extension Hext Har Hao).
    + exact Hframes.
    + unfold wakes_finished in *; unfold before, after, configuration in *; cbn in *.
      destruct ctrl; exact Hw.
  - intros x Hsolved; destruct (Hsummary x Hsolved) as [Hb|[result Hsaved]]; [now left|].
    right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - exact Hbounds.
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - eapply (@control_transport tf before after); [reflexivity|exact Hhistory|exact Hcontrol].
Qed.
Lemma dormant_saved_direct tf c owner direct : tf owner = Syntax.Ret direct ->
  D.leq direct (R.sigma_value (R.cfg_state c) owner) = true ->
  exists result, saved_observation tf c owner result.
Proof.
  intros Hbody Hdirect; exists {| Sem.Observation.observed_direct := direct;
    Sem.Observation.observed_reads := []; Sem.Observation.observed_sides := [];
    Sem.Observation.observed_spawns := [] |}; constructor; cbn.
  - now rewrite Hbody; constructor.
  - intros x v H; contradiction.
  - intros x v H; contradiction.
  - intros x H; contradiction.
  - exact Hdirect.
Qed.
Lemma remember_dormant_preserves tf roots st ctrl target : R.pure_bottom_rhs tf target = true ->
  invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (R.remember_dormant st target) ctrl).
Proof.
  intros Hpure Hinv; set (before := configuration st ctrl) in *;
    set (after := configuration (R.remember_dormant st target) ctrl).
  assert (Hdem : demand_transport before after).
  { intros x [H|[H|H]]; [left; now apply dormant_preserves|right; now left|right; now right]. }
  assert (Hhistory : history_transport before after None).
  { constructor.
    - intros x key value _ [Hp|[Hl Hr]]; [now left|right; split; [now apply dormant_lookup|exact Hr]].
    - intros; apply DL.leq_refl.
    - intros; apply DL.leq_refl.
    - intros x _ H; exact H.
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x [Hs|Hb]; [left; now apply dormant_preserves|now right]. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor; try assumption.
    + intros x H; change (S.mem x (S.add target (R.dormant_bottom st)) = true) in H.
      apply SL.add_spec in H as [->|H]; [exact Hpure|exact (Hd x H)].
    + intros x H; apply dormant_preserves; exact (Hframes x H).
  - intros x Hsolved; destruct (V.eq_dec x target) as [->|Hneq].
    + right; now apply dormant_saved.
    + assert (Hold : solved st x).
      { destruct Hsolved as [v H]; exists v; unfold R.semantic_lookup, R.remember_dormant in H; cbn in H.
        unfold R.semantic_lookup; destruct (M.lookup (R.sigma st) x); [exact H|].
        destruct (S.mem x (R.dormant_bottom st)) eqn:Hmem.
        - assert (S.mem x (S.add target (R.dormant_bottom st)) = true) by (apply SL.add_spec; now right).
          now rewrite H0 in H.
        -
        assert (S.mem x (S.add target (R.dormant_bottom st)) = false).
        { destruct (S.mem x (S.add target (R.dormant_bottom st))) eqn:Hadd; [|reflexivity].
          apply SL.add_spec in Hadd; intuition congruence. }
        rewrite H0 in H; discriminate. }
      destruct (Hsummary x Hold) as [Hb|[result Hsaved]]; [now left|].
      right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - exact Hbounds.
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - eapply (@control_transport tf before after); [reflexivity|exact Hhistory|exact Hcontrol].
Qed.

Lemma read_guard_flush st reader target value : read_guard st reader target value ->
  read_guard (R.flush_deferred st) reader target value.
Proof. intros [H|H]; [left; now apply flush_pending|now right]. Qed.
Lemma evaluation_execution_transport tf before after fr body :
  (forall target value, read_guard (R.cfg_state before) (R.frame_owner fr) target value ->
    read_guard (R.cfg_state after) (R.frame_owner fr) target value) ->
  (forall target, D.leq (R.stored_contribution (R.cfg_state before) (R.frame_owner fr) target)
    (R.stored_contribution (R.cfg_state after) (R.frame_owner fr) target) = true) ->
  (forall target, spawn_accounted before target -> spawn_accounted after target) ->
  evaluation tf before fr body -> evaluation tf after fr body.
Proof.
  intros Hreads Hsides Hspawns [reads [sides [spawns [Hp [Hr [Hl [Hpub [Htargets Hspawn]]]]]]]].
  exists reads, sides, spawns; split; [exact Hp|]; split.
  - intros x v H; apply Hreads; exact (Hr x v H).
  - split; [exact Hl|]; split.
    + intros target H; eapply DL.leq_trans; [exact (Hpub target H)|apply Hsides].
    + split; [exact Htargets|]; intros target H; apply Hspawns; exact (Hspawn target H).
Qed.
Lemma set_value_sigma_other st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  forall target, target <> R.frame_owner fr -> M.lookup (R.sigma next) target = M.lookup (R.sigma st) target.
Proof.
  intro H; apply set_value_cases in H as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; try trivial.
  intros target Hneq; unfold commit_publication; cbn; now rewrite ML.lookup_update_other.
Qed.
Lemma set_value_valuation_other st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  forall target, target <> R.frame_owner fr -> R.sigma_value next target = R.sigma_value st target.
Proof. intros H target Hneq; unfold R.sigma_value; now rewrite (@set_value_sigma_other st fr direct next next_fr H target Hneq). Qed.
Lemma set_value_readers_subset st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  forall target owner, S.mem owner (R.lookup_set (R.readers next) target) = true ->
    S.mem owner (R.lookup_set (R.readers st) target) = true.
Proof.
  intro H; apply set_value_cases in H as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; try trivial.
  intros target owner Hmem; unfold commit_publication, R.lookup_set in Hmem; cbn in Hmem.
  destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq].
  - rewrite ML.lookup_update_same, SL.empty_spec in Hmem; discriminate.
  - rewrite ML.lookup_update_other in Hmem by assumption; exact Hmem.
Qed.
Lemma publication_queue_ranked st owner value : ranked st owner -> ranked_list st (R.queue st) ->
  (forall reader, S.mem reader (R.lookup_set (R.readers st) owner) = true -> ranked st reader) ->
  ranked_list (commit_publication st owner value) (R.queue (commit_publication st owner value)).
Proof.
  intros Howner Hqueue Hreader; apply Forall_forall; intros target H.
  apply publication_members in H as [H|[H|[-> _]]].
  - exact (proj1 (Forall_forall _ _) Hqueue target H).
  - exact (Hreader target H).
  - exact Howner.
Qed.
Lemma publication_queue_ordered st owner value : ranked st owner -> ranked_list st (R.queue st) ->
  (forall reader, S.mem reader (R.lookup_set (R.readers st) owner) = true -> ranked st reader) ->
  RankLaws.valid (R.ranking st) -> sorted_queue st (R.queue st) ->
  sorted_queue (commit_publication st owner value) (R.queue (commit_publication st owner value)).
Proof.
  intros Howner Hqueue Hreader Hv Hordered.
  assert (Hreaders : ranked_list st (S.elements (R.lookup_set (R.readers st) owner))).
  { apply Forall_forall; intros reader H; apply Hreader; now apply SL.mem_spec. }
  pose proof (queue_many_ranked Hreaders Hqueue) as Hmany.
  pose proof (queue_many_sorted Hreaders Hqueue Hv Hordered) as Horder.
  change (sorted_queue st (R.queue (commit_publication st owner value))).
  unfold commit_publication; cbn; destruct (S.mem owner (R.controlled st) && Features.recompute_controlled);
    [now apply queue_insert_sorted|exact Horder].
Qed.
Lemma set_value_queue_shape st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  ranked st (R.frame_owner fr) -> ranked_list st (R.queue st) ->
  (forall reader, S.mem reader (R.lookup_set (R.readers st) (R.frame_owner fr)) = true -> ranked st reader) ->
  RankLaws.valid (R.ranking st) -> sorted_queue st (R.queue st) ->
  ranked_list next (R.queue next) /\ sorted_queue next (R.queue next).
Proof.
  intros H Howner Hqueue Hreader Hv Horder;
    apply set_value_cases in H as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; try (now split).
  split; [now apply publication_queue_ranked|now apply publication_queue_ordered].
Qed.

Lemma set_value_frame_view st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  R.frame_owner next_fr = R.frame_owner fr /\ R.frame_local_side next_fr = R.frame_local_side fr /\
  R.frame_current_targets next_fr = R.frame_current_targets fr.
Proof.
  intro H; apply set_value_cases in H as [[_ [_ ->]]|[_ [-> _]]]; repeat split; reflexivity.
Qed.
Lemma commit_preserves tf roots st fr direct k next next_fr :
  R.set_value (R.flush_deferred st) fr direct = (next,next_fr) ->
  invariant tf roots (configuration st (R.RunCommit fr direct k)) ->
  invariant tf roots (configuration next (R.RunDrain next_fr k)).
Proof.
  intros Hwrite Hinv; set (before := configuration st (R.RunCommit fr direct k)) in *;
    set (after := configuration next (R.RunDrain next_fr k)).
  destruct (@set_value_metadata (R.flush_deferred st) fr direct next next_fr Hwrite) as [Hrank [Hside [Hdormant [Hwake [Hfifo Hrequested]]]]].
  destruct (@set_value_frame_view (R.flush_deferred st) fr direct next next_fr Hwrite) as [Howner [Hlocal Htargets]].
  change (R.ranking next = R.ranking st) in Hrank;
    change (R.contributions next = R.contributions st) in Hside;
    change (R.dormant_bottom next = R.dormant_bottom st) in Hdormant;
    change (R.deferred_wakes next = []) in Hwake;
    change (R.pending_spawns next = R.pending_spawns st) in Hfifo;
    change (R.requested_spawns next = R.requested_spawns st) in Hrequested.
  assert (Hpending : forall x, pending st x -> pending next x).
  { intros x H; eapply (@set_value_pending _ fr direct next next_fr); [exact Hwrite|now apply flush_pending]. }
  assert (Hsolves : forall x, solved st x -> solved next x).
  { intros x H; eapply (@set_value_solved _ fr direct next next_fr); [exact Hwrite|exact H]. }
  assert (Hbusy : forall x, busy before x -> busy after x).
  { intros x [Hp|Ha]; [left; now apply Hpending|right].
    unfold before, after, configuration in *; cbn in *; now rewrite Howner. }
  assert (Hdem : demand_transport before after).
  { intros x [H|[H|H]]; [left; now apply Hsolves|right; left; now apply Hbusy|right; right; exact H]. }
  assert (Hlookup_other : forall x, x <> R.frame_owner fr -> R.semantic_lookup next x = R.semantic_lookup st x).
  { intros x H; exact (@set_value_other_lookup (R.flush_deferred st) fr direct next next_fr Hwrite x H). }
  assert (Hvalue_other : forall x, x <> R.frame_owner fr -> R.sigma_value next x = R.sigma_value st x).
  { intros x H; exact (@set_value_valuation_other (R.flush_deferred st) fr direct next next_fr Hwrite x H). }
  assert (Hreads : forall reader target value, read_guard st reader target value -> read_guard next reader target value).
  { intros reader target value H; eapply (@set_value_read_guard _ fr direct next next_fr);
      [exact Hwrite|now apply read_guard_flush]. }
  assert (Hspawns : forall target, spawn_accounted before target -> spawn_accounted after target).
  { apply spawn_transport; [exact Hdem|].
    intros x H; change (S.mem x (R.requested_spawns next) = true); now rewrite Hrequested. }
  assert (Hhistory : history_transport before after (Some (R.frame_owner fr))).
  { constructor.
    - intros x target value _ H; now apply Hreads.
    - intros x target _; unfold before, after, configuration, R.stored_contribution; cbn; rewrite Hside; apply DL.leq_refl.
    - intros x Hneq; unfold before, after, configuration; cbn; rewrite Hvalue_other by congruence; apply DL.leq_refl.
    - intros x Hneq [Hp|[Hnot|Hb]].
      + left; now apply Hpending.
      + right; left; intro H; change (In x (R.frame_owner next_fr :: suspended_owners k)) in H;
          rewrite Howner in H; exact (Hnot H).
      + right; right; unfold before, after, configuration, R.aggregate in *; cbn in *;
          rewrite Hside, Hvalue_other by congruence; exact Hb.
    - exact Hspawns.
    - intros x [Hs|Hb]; [left; now apply Hsolves|right; now apply Hbusy]. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol].
  destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw].
  assert (Hrank_owner : ranked st (R.frame_owner fr)).
  { change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in Har; now inversion Har. }
  assert (Hqueue_shape : ranked_list next (R.queue next) /\ sorted_queue next (R.queue next)).
  { eapply (@set_value_queue_shape (R.flush_deferred st) fr direct next next_fr).
    - exact Hwrite.
    - exact Hrank_owner.
    - exact (queue_many_ranked Hwr Hqr).
    - intros reader H; exact (Hr (R.frame_owner fr) reader H).
    - exact Hv.
    - exact (queue_many_sorted Hwr Hqr Hv Hqo). }
  constructor.
  - constructor.
    + change (RankLaws.valid (R.ranking next)); now rewrite Hrank.
    + intros x H; unfold after, configuration in H |- *; cbn in H |- *; unfold ranked; rewrite Hrank.
      destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq]; [exact Hrank_owner|].
      apply Hlive; unfold R.is_materialized in H |- *.
      now rewrite (@set_value_sigma_other _ fr direct next next_fr Hwrite x Hneq) in H.
    + intros x H; apply Hd; unfold after, configuration in H; cbn in H; now rewrite Hdormant in H.
    + intros target x H; unfold after, configuration in H |- *; cbn in H |- *; unfold ranked; rewrite Hrank.
      apply Hr with target; exact (@set_value_readers_subset _ fr direct next next_fr Hwrite target x H).
    + exact (proj1 Hqueue_shape).
    + change (ranked_list next (R.deferred_wakes next)); rewrite Hwake; constructor.
    + exact (proj2 Hqueue_shape).
    + change (sorted_queue next (R.deferred_wakes next)); rewrite Hwake; constructor.
    + unfold after, configuration, active_owners, ranked_list, ranked; cbn; rewrite Howner, Hrank; exact Har.
    + unfold after, configuration, active_owners, sorted_queue, priority; cbn; rewrite Howner, Hrank; exact Hao.
    + intros x H; apply Hsolves; apply Hframes.
      unfold after, before, configuration in H |- *; cbn in H |- *; now rewrite Howner in H.
    + exact Hwake.
  - intros x Hsolved; destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq].
    + left; right; unfold after, configuration; cbn; rewrite Howner; now left.
    + assert (Hold : solved st x) by (destruct Hsolved as [value H]; exists value; now rewrite Hlookup_other in H).
      destruct (Hsummary x Hold) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
      right; exists result; eapply (@saved_transport tf before after (Some (R.frame_owner fr)));
        [exact Hhistory|congruence|exact Hsaved].
  - intros x; destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq].
    + left; right; unfold after, configuration; cbn; rewrite Howner; now left.
    + destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|right].
      unfold after, configuration; cbn; unfold R.aggregate; rewrite Hside, Hvalue_other by assumption; exact Hb.
  - eapply (@requests_transport before after); [exact Hdem|exact Hrequested| |exact Hreq].
    intros x H; left; unfold after, configuration; cbn; now rewrite Hfifo.
  - exact (seeds_transport Hdem Hroots).
  - unfold after, configuration, control_valid; cbn; destruct Hcontrol as [He Hk]; split.
    + assert (He_after : evaluation tf after fr (Syntax.Ret direct)).
      { eapply (@evaluation_execution_transport tf before after fr (Syntax.Ret direct));
          [exact (Hreads (R.frame_owner fr))| |exact Hspawns|exact He].
        intros target; unfold before, after, configuration, R.stored_contribution; cbn; rewrite Hside; apply DL.leq_refl. }
      assert (He_frame : evaluation tf after next_fr (Syntax.Ret direct)).
      { eapply evaluation_frame; [symmetry; exact Howner|symmetry; exact Hlocal|symmetry; exact Htargets|exact He_after]. }
      destruct (@set_value_bound (R.flush_deferred st) fr direct next next_fr Hwrite) as [Hdirect Haggregate].
      apply completed_from_evaluation with direct; [exact He_frame|now rewrite Howner|right; right; now rewrite Howner].
    + eapply (@continuation_transport tf before after (Some (R.frame_owner fr)) k); [exact Hhistory| |exact Hk].
      intros x Hin Heq; inversion Heq; subst; exact (@stack_owner_not_suspended st (R.frame_owner fr) k Hao Hin).
Qed.

Lemma release_preserves tf roots st fr k : ~ In (R.frame_owner fr) (R.queue st) ->
  invariant tf roots (configuration st (R.RunDrain fr k)) ->
  invariant tf roots (configuration st (R.Return k)).
Proof.
  intros Habsent Hinv; set (before := configuration st (R.RunDrain fr k)) in *;
    set (after := configuration st (R.Return k)).
  assert (Hlive : solved st (R.frame_owner fr)).
  { apply (shape_live_frames (inv_shape Hinv)); change (In (R.frame_owner fr) (R.frame_owner fr :: suspended_owners k)); now left. }
  assert (Hbusy : forall x, x <> R.frame_owner fr -> busy before x -> busy after x).
  { intros x Hneq [Hp|Ha]; [now left|right].
    change (In x (R.frame_owner fr :: suspended_owners k)) in Ha;
      destruct Ha as [E|H]; [congruence|exact H]. }
  assert (Hdem : demand_transport before after).
  { intros x [H|[H|H]]; [now left| |right; now right].
    destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq]; [left; exact Hlive|right; left; exact (Hbusy x Hneq H)]. }
  assert (Hhistory : history_transport before after None).
  { apply transport_unchanged; try reflexivity.
    - intros; assumption.
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x [Hs|Hb]; [now left|].
      destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq]; [left; exact Hlive|right; exact (Hbusy x Hneq Hb)].
    - intros x _ H; change (In x (R.frame_owner fr :: suspended_owners k)); now right. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol].
  destruct Hshape as [Hv Hmaterial Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw].
  destruct Hcontrol as [[result [Hsaved Hincoming]] Hk]; constructor.
  - constructor; try assumption.
    + change (ranked_list st (suspended_owners k)); change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in Har.
      now inversion Har.
    + change (sorted_queue st (suspended_owners k)); change (sorted_queue st (R.frame_owner fr :: suspended_owners k)) in Hao.
      now inversion Hao.
    + intros x H; apply Hframes; change (In x (R.frame_owner fr :: suspended_owners k)); now right.
  - intros x Hsolved; destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq].
    + right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
    + destruct (Hsummary x Hsolved) as [Hb|[observation Hcertificate]]; [left; exact (Hbusy x Hneq Hb)|].
      right; exists observation; eapply (@saved_transport tf before after None);
        [exact Hhistory|discriminate|exact Hcertificate].
  - intros x; destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq].
    + destruct Hincoming as [[Hqueue|Hwake]|[Hnot|Hbound]].
      * contradiction.
      * change (R.deferred_wakes st = []) in Hw; change (In (R.frame_owner fr) (R.deferred_wakes st)) in Hwake;
        rewrite Hw in Hwake; contradiction.
      * exfalso; apply Hnot; change (In (R.frame_owner fr) (R.frame_owner fr :: suspended_owners k)); now left.
      * right; exact Hbound.
    + destruct (Hbounds x) as [Hb|Hb]; [left; exact (Hbusy x Hneq Hb)|now right].
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - change (continuation_valid tf after k); eapply (@continuation_transport tf before after None k);
      [exact Hhistory|discriminate|exact Hk].
Qed.
Lemma drain_lower_absent st fr head tail : RankLaws.valid (R.ranking st) ->
  ranked st (R.frame_owner fr) -> ranked st head -> sorted_queue st (head :: tail) ->
  head <> R.frame_owner fr -> R.rank_lt st (R.frame_owner fr) head = false ->
  ~ In (R.frame_owner fr) (head :: tail).
Proof.
  intros Hv Howner Hhead Horder Hneq Hlt; apply (@queue_below_absent st (R.frame_owner fr) head tail); [exact Horder|].
  apply (proj1 (compare_rank_false Howner Hhead)) in Hlt.
  assert (priority st head <> priority st (R.frame_owner fr)).
  { intro Heq; apply Hneq; exact (@priority_distinct st head (R.frame_owner fr) Hv Hhead Howner Heq). }
  lia.
Qed.
Lemma reset_preserves tf roots st ctrl scope : invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (R.reset_registered_cells st scope) ctrl).
Proof.
  intro Hinv; pose proof (reset_cells_view st scope ctrl) as Hv.
  use_invariant_view Hinv; [exact Hv| | |exact Hinv].
  - pose proof (view_wakes Hv) as Hwv.
    change (R.deferred_wakes (R.reset_registered_cells st scope) = R.deferred_wakes st) in Hwv.
    unfold wakes_finished, configuration; cbn; destruct ctrl; cbn; trivial; now rewrite Hwv.
  - eapply (@control_transport tf (configuration st ctrl) (configuration (R.reset_registered_cells st scope) ctrl));
      [reflexivity|exact (history_view Hv)|exact (inv_control Hinv)].
Qed.
Lemma drain_empty_preserves tf roots st fr k : R.queue st = [] ->
  invariant tf roots (configuration st (R.RunDrain fr k)) ->
  invariant tf roots (configuration (R.reset_registered_cells st (R.frame_owner fr)) (R.Return k)).
Proof.
  intros Hqueue Hinv; apply reset_preserves; apply (@release_preserves tf roots st fr k); [now rewrite Hqueue|exact Hinv].
Qed.
Lemma drain_lower_preserves tf roots st fr k head tail : R.queue st = head :: tail ->
  head <> R.frame_owner fr -> R.rank_lt st (R.frame_owner fr) head = false ->
  invariant tf roots (configuration st (R.RunDrain fr k)) ->
  invariant tf roots (configuration (R.reset_registered_cells st (R.frame_owner fr)) (R.Return k)).
Proof.
  intros Hqueue Hneq Hlt Hinv; apply reset_preserves; apply (@release_preserves tf roots st fr k); [|exact Hinv].
  rewrite Hqueue; eapply drain_lower_absent; [exact (shape_ranks (inv_shape Hinv))| | | |exact Hneq|exact Hlt].
  - pose proof (shape_stack_ranks (inv_shape Hinv)) as H; change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in H.
    now inversion H.
  - pose proof (shape_queue_ranks (inv_shape Hinv)) as H; change (ranked_list st (R.queue st)) in H; rewrite Hqueue in H.
    now inversion H.
  - pose proof (shape_queue_order (inv_shape Hinv)) as H; change (sorted_queue st (R.queue st)) in H; now rewrite Hqueue in H.
Qed.

Lemma request_state_preserves tf roots st ctrl target : invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (R.request_spawn st target) ctrl).
Proof.
  intro Hinv; unfold R.request_spawn; destruct (S.mem target (R.requested_spawns st)) eqn:Hseen; [exact Hinv|].
  set (before := configuration st ctrl) in *;
    set (after := configuration (R.with_spawns st (R.pending_spawns st ++ [target]) (S.add target (R.requested_spawns st))) ctrl).
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [split; reflexivity|intros; right; now left|intros; right; now right]. }
  assert (Hhistory : history_transport before after None).
  { apply transport_unchanged; try reflexivity.
    - intros; assumption.
    - apply spawn_transport; [exact Hdem|]. intros x H; apply SL.add_spec; now right.
    - intros x H; exact H.
    - intros x _ H; exact H. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape; constructor; assumption.
  - intros x Hsolved; destruct (Hsummary x Hsolved) as [Hb|[result Hsaved]]; [now left|].
    right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - exact Hbounds.
  - intros x H; change (S.mem x (S.add target (R.requested_spawns st)) = true) in H.
    apply SL.add_spec in H as [->|H].
    + left; change (In target (R.pending_spawns st ++ [target])); apply in_app_iff; right; now left.
    + destruct (Hreq x H) as [Hp|Hd]; [left; apply in_app_iff; now left|right; now apply Hdem].
  - exact (seeds_transport Hdem Hroots).
  - eapply (@control_transport tf before after); [reflexivity|exact Hhistory|exact Hcontrol].
Qed.
Lemma deferred_spawn_preserves tf roots st fr target tail k :
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  invariant tf roots (configuration (R.request_spawn st target) (R.RunRhs fr tail k)).
Proof.
  intro Hinv; pose proof (@request_state_preserves tf roots st (R.RunRhs fr (Syntax.Spawn target tail) k) target Hinv) as Hreq.
  assert (Hv : logical_view (configuration (R.request_spawn st target) (R.RunRhs fr (Syntax.Spawn target tail) k))
    (configuration (R.request_spawn st target) (R.RunRhs fr tail k))) by (apply control_view; reflexivity).
  use_invariant_view Hreq; [exact Hv|intros; exact I| |exact Hreq].
  destruct (inv_control Hreq) as [He Hk]; split.
  - apply evaluation_spawn with target.
    + eapply evaluation_view; [exact Hv|exact He].
    + right; change (S.mem target (R.requested_spawns (R.request_spawn st target)) = true).
      apply requested_add; now left.
  - eapply continuation_view; [exact Hv|exact Hk].
Qed.
Lemma skip_seed_preserves tf roots st owner remaining : solved st owner ->
  invariant tf roots (configuration st (R.RunSeeds (owner::remaining))) ->
  invariant tf roots (configuration st (R.RunSeeds remaining)).
Proof.
  intros Hsolved Hinv; set (before := configuration st (R.RunSeeds (owner::remaining))) in *;
    set (after := configuration st (R.RunSeeds remaining)).
  assert (Hdem : demand_transport before after).
  { intros x [H|[H|H]]; [now left|right; now left|].
    change (In x (owner::remaining)) in H; destruct H as [->|H]; [left; exact Hsolved|right; right; exact H]. }
  assert (Hhistory : history_transport before after None).
  { apply transport_unchanged; try reflexivity.
    - intros; assumption.
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x H; exact H.
    - intros x _ H; exact H. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape; constructor; assumption.
  - intros x H; destruct (Hsummary x H) as [Hb|[result Hsaved]]; [now left|].
    right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - exact Hbounds.
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - exact I.
Qed.
Lemma empty_seeds_preserves tf roots st : invariant tf roots (configuration st (R.RunSeeds [])) ->
  invariant tf roots (configuration st R.RunLoop).
Proof.
  intro H; use_invariant_view H; [apply control_view; reflexivity| |exact I|exact H].
  unfold wakes_finished, configuration; cbn; trivial.
Qed.
Lemma seed_loop_idle_preserves tf roots st remaining :
  invariant tf roots (configuration st (R.RunSeedLoop remaining)) ->
  invariant tf roots (configuration st (R.RunSeeds remaining)).
Proof.
  intro H; use_invariant_view H; [apply control_view; reflexivity| |exact I|exact H].
  unfold wakes_finished, configuration; cbn; trivial.
Qed.
Lemma fifo_start_preserves tf roots st target remaining : R.pending_spawns st = target :: remaining ->
  invariant tf roots (configuration st R.RunLoop) ->
  invariant tf roots (configuration (R.with_spawns st remaining (R.requested_spawns st)) (R.RunSeeds [target])).
Proof.
  intros Hfifo Hinv; set (before := configuration st R.RunLoop) in *;
    set (after := configuration (R.with_spawns st remaining (R.requested_spawns st)) (R.RunSeeds [target])).
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [split; reflexivity|intros; right; now left|intros x H; contradiction]. }
  assert (Hhistory : history_transport before after None).
  { apply transport_unchanged; try reflexivity.
    - intros; assumption.
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x H; exact H.
    - intros x _ H; exact H. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape; constructor; assumption.
  - intros x H; destruct (Hsummary x H) as [Hb|[result Hsaved]]; [now left|].
    right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - exact Hbounds.
  - eapply (@requests_transport before after); [exact Hdem|reflexivity| |exact Hreq].
    intros x H; change (In x (R.pending_spawns st)) in H; rewrite Hfifo in H.
    destruct H as [->|H]; [right; right; right; now left|now left].
  - exact (seeds_transport Hdem Hroots).
  - exact I.
Qed.
Lemma start_seed_preserves tf roots st owner remaining : ranked st owner ->
  invariant tf roots (configuration st (R.RunSeeds (owner::remaining))) ->
  invariant tf roots (configuration st (R.StartEpisode owner (R.KSeedLoop remaining))).
Proof.
  intros Hrank Hinv; set (before := configuration st (R.RunSeeds (owner::remaining))) in *;
    set (after := configuration st (R.StartEpisode owner (R.KSeedLoop remaining))).
  assert (Hbusy : forall x, busy before x -> busy after x).
  { intros x [H|H]; [now left|contradiction]. }
  assert (Hdem : demand_transport before after).
  { intros x [H|[H|H]]; [now left|right; left; now apply Hbusy|].
    change (In x (owner::remaining)) in H; destruct H as [->|H]; [right; left; right; now left|right; right; exact H]. }
  assert (Hhistory : history_transport before after None).
  { apply transport_unchanged; try reflexivity.
    - intros; assumption.
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x [Hs|Hb]; [now left|right; now apply Hbusy].
    - intros x _ H; exact H. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape; constructor; try assumption.
    + constructor; [exact Hrank|constructor].
    + constructor; constructor.
  - intros x H; destruct (Hsummary x H) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
    right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - intros x; destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|now right].
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - exact I.
Qed.

Lemma above_stack st owner owners child : sorted_queue st (owner :: owners) ->
  priority st owner < priority st child ->
  forall x, In x (owner :: owners) -> priority st x < priority st child.
Proof. intros Hsort Hgreater x Hin; pose proof (sorted_head_max Hsort Hin); lia. Qed.
Lemma push_history st ctrl child k : active_owners ctrl = suspended_owners k -> framed_owners ctrl = suspended_owners k ->
  seed_owners ctrl = suspended_seeds k ->
  history_transport (configuration st ctrl) (configuration st (R.StartEpisode child k)) None.
Proof.
  intros Ha Hf Hs; apply transport_unchanged; try reflexivity.
  - intros; assumption.
  - apply spawn_transport; [|intros; assumption]; apply demand_same_store; [split; reflexivity| |].
    + intros x [Hpending|Hactive]; right; left; [now left|right].
      change (In x (child :: suspended_owners k)); right; now rewrite <- Ha.
    + intros x H; right; right; change (In x (suspended_seeds k)); now rewrite <- Hs.
  - intros x [Hsolved|[Hpending|Hactive]]; [now left|right; now left|right; right].
    change (In x (child :: suspended_owners k)); right; now rewrite <- Ha.
  - intros x _ H; change (In x (framed_owners ctrl)); now rewrite Hf.
Qed.
Lemma push_child_preserves tf roots st ctrl child k :
  active_owners ctrl = suspended_owners k -> framed_owners ctrl = suspended_owners k ->
  seed_owners ctrl = suspended_seeds k -> ranked st child ->
  (forall owner, In owner (suspended_owners k) -> priority st owner < priority st child) ->
  continuation_valid tf (configuration st (R.StartEpisode child k)) k ->
  invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration st (R.StartEpisode child k)).
Proof.
  intros Ha Hf Hs Hrank Habove Hkont Hinv; set (before := configuration st ctrl) in *;
    set (after := configuration st (R.StartEpisode child k)).
  assert (Hbusy : forall x, busy before x -> busy after x).
  { intros x [Hp|H]; [now left|right]. change (In x (child :: suspended_owners k)); right.
    change (In x (active_owners ctrl)) in H; now rewrite <- Ha. }
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [split; reflexivity|intros; right; left; now apply Hbusy|].
    intros x H; right; right; change (In x (suspended_seeds k)); now rewrite <- Hs. }
  pose proof (@push_history st ctrl child k Ha Hf Hs) as Hhistory.
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor; try assumption.
    + change (ranked_list st (child :: suspended_owners k)); constructor; [exact Hrank|].
      change (ranked_list st (active_owners ctrl)) in Har; now rewrite <- Ha.
    + change (sorted_queue st (child :: suspended_owners k)); constructor.
      * change (sorted_queue st (active_owners ctrl)) in Hao; now rewrite <- Ha.
      * apply Forall_forall; exact Habove.
    + intros x H; apply Hframes; change (In x (framed_owners ctrl)); now rewrite Hf.
    + exact I.
  - intros x H; destruct (Hsummary x H) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
    right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - intros x; destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|now right].
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - exact Hkont.
Qed.
Lemma get_child_preserves tf roots st fr target tail k : ranked st target ->
  R.rank_lt st (R.frame_owner fr) target = true ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  invariant tf roots (configuration st (R.StartEpisode target (R.KAfterGet fr target tail k))).
Proof.
  intros Htarget Hgreater Hinv.
  pose proof (shape_stack_ranks (inv_shape Hinv)) as Hr;
    change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in Hr; inversion Hr; subst.
  assert (Howner : ranked st (R.frame_owner fr)) by assumption.
  apply (proj1 (compare_rank Howner Htarget)) in Hgreater.
  eapply (@push_child_preserves tf roots st (R.RunRhs fr (Syntax.Get target tail) k)
    target (R.KAfterGet fr target tail k)); try reflexivity.
  - exact Htarget.
  - exact (@above_stack st (R.frame_owner fr) (suspended_owners k) target (shape_stack_order (inv_shape Hinv)) Hgreater).
  - pose proof (@push_history st (R.RunRhs fr (Syntax.Get target tail) k) target
      (R.KAfterGet fr target tail k) eq_refl eq_refl eq_refl) as Hhistory.
    destruct (inv_control Hinv) as [He Hk]; split.
    + eapply (@evaluation_transport tf _ _ None); [exact Hhistory|discriminate|exact He].
    + split; [right; right; change (In target (target :: R.frame_owner fr :: suspended_owners k)); now left|].
      eapply (@continuation_transport tf _ _ None); [exact Hhistory|discriminate|exact Hk].
  - exact Hinv.
Qed.

Lemma same_control_preserves tf roots before after : logical_view before after ->
  R.cfg_control after = R.cfg_control before -> invariant tf roots before -> invariant tf roots after.
Proof.
  intros Hv Hctrl Hinv; eapply (@invariant_view tf roots before after); [exact Hv| | |exact Hinv].
  - unfold wakes_finished; rewrite Hctrl; destruct (R.cfg_control before); try trivial;
      now rewrite (view_wakes Hv).
  - eapply (@control_transport tf before after); [exact Hctrl|exact (history_view Hv)|exact (inv_control Hinv)].
Qed.
Lemma controlled_preserves tf roots st ctrl target : invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (R.promote_controlled st target) ctrl).
Proof.
  intro Hinv; eapply (@same_control_preserves tf roots (configuration st ctrl)
    (configuration (R.promote_controlled st target) ctrl)); [constructor; reflexivity|reflexivity|exact Hinv].
Qed.
Lemma reader_state_preserves tf roots st ctrl target owner : ranked st owner ->
  invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (R.add_reader st target owner) ctrl).
Proof.
  intros Howner Hinv; set (before := configuration st ctrl) in *;
    set (after := configuration (R.add_reader st target owner) ctrl).
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [split; reflexivity|intros; right; now left|intros; right; now right]. }
  assert (Hhistory : history_transport before after None).
  { constructor.
    - intros x key value _ [Hp|[Hl Hr]]; [now left|right; split; [exact Hl|]].
      change (S.mem x (R.lookup_set (R.readers (R.add_reader st target owner)) key) = true).
      destruct (V.eq_dec key target) as [->|Hneq].
      + apply reader_mem_add; now right.
      + rewrite reader_mem_other by congruence; exact Hr.
    - intros; apply DL.leq_refl.
    - intros; apply DL.leq_refl.
    - intros x _ H; exact H.
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x H; exact H. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor; try assumption.
    intros key reader H; change (S.mem reader (R.lookup_set (R.readers (R.add_reader st target owner)) key) = true) in H.
    destruct (V.eq_dec key target) as [->|Hneq].
    + apply reader_mem_add in H as [->|H]; [exact Howner|exact (Hr target reader H)].
    + rewrite reader_mem_other in H by congruence; exact (Hr key reader H).
  - intros x Hsolved; destruct (Hsummary x Hsolved) as [Hb|[result Hsaved]]; [now left|].
    right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - exact Hbounds.
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - eapply (@control_transport tf before after); [reflexivity|exact Hhistory|exact Hcontrol].
Qed.
Lemma enqueue_state_preserves tf roots st ctrl target : ranked st target ->
  invariant tf roots (configuration st ctrl) -> invariant tf roots (configuration (R.enqueue st target) ctrl).
Proof.
  intros Htarget Hinv; set (before := configuration st ctrl) in *;
    set (after := configuration (R.enqueue st target) ctrl).
  assert (Hbusy : forall x, busy before x -> busy after x).
  { intros x [Hp|Ha]; [left; now apply queue_preserves_pending|now right]. }
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [split; reflexivity|intros; right; left; now apply Hbusy|intros; right; now right]. }
  assert (Hhistory : history_transport before after None).
  { apply transport_unchanged; try reflexivity.
    - intros x _ H; now apply queue_preserves_pending.
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x [Hs|Hb]; [now left|right; now apply Hbusy].
    - intros x _ H; exact H. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor; try assumption.
    + apply Forall_forall; intros x H; apply queue_insert_members in H as [->|H]; [exact Htarget|].
      exact (proj1 (Forall_forall _ _) Hqr x H).
    + change (sorted_queue st (R.queue_insert (R.ranking st) target (R.queue st))); now apply queue_insert_sorted.
  - intros x Hsolved; destruct (Hsummary x Hsolved) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
    right; exists result; eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - intros x; destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|now right].
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - eapply (@control_transport tf before after); [reflexivity|exact Hhistory|exact Hcontrol].
Qed.
Lemma materialize_state_preserves tf roots st ctrl target : ranked st target ->
  ready (configuration st ctrl) target -> invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (R.materialize st target) ctrl).
Proof.
  intros Hrank Hready Hinv; unfold R.materialize; destruct (M.lookup (R.sigma st) target) eqn:Hlookup; [exact Hinv|].
  set (prepared := R.with_sigma st (M.update (R.sigma st) target D.bottom)).
  set (before := configuration st ctrl) in *; set (after := configuration prepared ctrl).
  assert (Hvalue : forall x, R.sigma_value prepared x = R.sigma_value st x).
  { intros x; destruct (V.eq_dec x target) as [->|Hneq].
    - unfold prepared; rewrite sigma_write_same; unfold R.sigma_value; now rewrite Hlookup.
    - unfold prepared; now apply sigma_write_other. }
  assert (Hsolves : forall x, solved st x -> solved prepared x) by (intros; now apply sigma_write_preserves).
  assert (Hlookup_preserved : forall x value, R.semantic_lookup st x = Some value -> R.semantic_lookup prepared x = Some value).
  { intros x value H; pose proof (@materialize_lookup st target x value H) as Hm.
    unfold R.materialize in Hm; now rewrite Hlookup in Hm. }
  assert (Hdem : demand_transport before after).
  { intros x [H|[H|H]]; [left; now apply Hsolves|right; now left|right; now right]. }
  assert (Hhistory : history_transport before after None).
  { constructor.
    - intros x key value _ [Hp|[Hl Hr]]; [now left|right; split; [now apply Hlookup_preserved|exact Hr]].
    - intros; apply DL.leq_refl.
    - intros x _; unfold before, after, configuration; cbn; rewrite Hvalue; apply DL.leq_refl.
    - intros x _ [Hp|[Hnot|Hb]]; [now left|right; now left|right; right];
        unfold before, after, configuration in *; cbn in *; now rewrite Hvalue.
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x [Hs|Hb]; [left; now apply Hsolves|now right]. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor; try assumption.
    + intros x H; destruct (V.eq_dec x target) as [->|Hneq]; [exact Hrank|].
      apply Hlive; unfold R.is_materialized in H |- *; unfold after, configuration, prepared in H; cbn in H.
      now rewrite ML.lookup_update_other in H.
    + intros x H; apply Hsolves; exact (Hframes x H).
  - intros x Hsolved; assert (Hcase : solved st x \/ x = target).
    { destruct (V.eq_dec x target) as [->|Hneq]; [now right|left].
      destruct Hsolved as [v H]; exists v; unfold after, configuration, prepared, R.semantic_lookup in H; cbn in H.
      now rewrite ML.lookup_update_other in H. }
    destruct Hcase as [Hold|Heq].
    + destruct (Hsummary x Hold) as [Hb|[result Hsaved]]; [now left|right; exists result].
      eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
    + subst x; destruct Hready as [Hold|Hbusy]; [|now left].
      destruct (Hsummary target Hold) as [Hb|[result Hsaved]]; [now left|right; exists result].
      eapply (@saved_transport tf before after None); [exact Hhistory|discriminate|exact Hsaved].
  - intros x; destruct (Hbounds x) as [Hb|Hb]; [now left|right].
    unfold after, configuration; cbn; rewrite Hvalue; exact Hb.
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - eapply (@control_transport tf before after); [reflexivity|exact Hhistory|exact Hcontrol].
Qed.

Lemma complete_get_state_preserves tf roots st ctrl fr target next next_fr value :
  R.complete_get st fr target = (next,next_fr,value) -> ranked st target -> ranked st (R.frame_owner fr) ->
  ready (configuration st ctrl) target -> invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration next ctrl).
Proof.
  unfold R.complete_get; destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hrank;
    intros Hwrite Htarget Howner Hready Hinv; inversion Hwrite; subst.
  all: apply materialize_state_preserves; [exact Htarget|exact Hready|].
  - apply reader_state_preserves; [exact Howner|exact Hinv].
  - change (invariant tf roots (configuration (R.add_reader (R.promote_controlled st target) target (R.frame_owner fr)) ctrl)).
    apply (@reader_state_preserves tf roots (R.promote_controlled st target) ctrl target (R.frame_owner fr));
      [exact Howner|now apply controlled_preserves].
Qed.
Lemma materialize_readers st target : R.readers (R.materialize st target) = R.readers st.
Proof. unfold R.materialize; destruct (M.lookup (R.sigma st) target); reflexivity. Qed.
Lemma complete_get_observed st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  R.semantic_lookup next target = Some value /\ S.mem (R.frame_owner fr) (R.lookup_set (R.readers next) target) = true.
Proof.
  unfold R.complete_get; intro H; inversion H; subst; split.
  - apply solved_value; apply materialize_solves.
  - rewrite materialize_readers; unfold R.lookup_set; cbn; rewrite ML.lookup_update_same; apply SL.add_spec; now left.
Qed.
Lemma complete_get_frame_view st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  R.frame_owner next_fr = R.frame_owner fr /\ R.frame_local_side next_fr = R.frame_local_side fr /\
  R.frame_current_targets next_fr = R.frame_current_targets fr.
Proof. unfold R.complete_get; intro H; inversion H; subst; repeat split; reflexivity. Qed.
Definition read_control (waiting : bool) fr target tail k :=
  if waiting then R.Return (R.KAfterGet fr target tail k) else R.RunRhs fr (Syntax.Get target tail) k.
Lemma complete_get_cursor_preserves tf roots st waiting fr target tail k next next_fr value :
  R.complete_get st fr target = (next,next_fr,value) -> ranked st target ->
  ready (configuration st (read_control waiting fr target tail k)) target ->
  invariant tf roots (configuration st (read_control waiting fr target tail k)) ->
  invariant tf roots (configuration next (R.RunRhs next_fr (tail value) k)).
Proof.
  intros Hwrite Htarget Hready Hinv.
  assert (Howner_rank : ranked st (R.frame_owner fr)).
  { pose proof (shape_stack_ranks (inv_shape Hinv)) as H; unfold read_control in H; destruct waiting;
      change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in H; now inversion H. }
  pose proof (@complete_get_state_preserves tf roots st (read_control waiting fr target tail k)
    fr target next next_fr value Hwrite Htarget Howner_rank Hready Hinv) as Hupdated.
  set (middle := configuration next (read_control waiting fr target tail k)) in Hupdated.
  set (after := configuration next (R.RunRhs next_fr (tail value) k)).
  destruct (@complete_get_frame_view st fr target next next_fr value Hwrite) as [Howner [Hlocal Htargets]].
  assert (Hv : logical_view middle after).
  { unfold middle, after; apply control_view; unfold read_control; destruct waiting;
      cbn [active_owners framed_owners seed_owners suspended_owners suspended_seeds];
      rewrite ?Howner; reflexivity. }
  assert (Hcursor : evaluation tf middle fr (Syntax.Get target tail) /\ continuation_valid tf middle k).
  { pose proof (inv_control Hupdated) as H; unfold middle, read_control, control_valid, configuration in H.
    destruct waiting; cbn in H; [destruct H as [He [_ Hk]]; now split|exact H]. }
  use_invariant_view Hupdated; [exact Hv|intros; exact I| |exact Hupdated].
  destruct Hcursor as [He Hk]; unfold after, configuration, control_valid; cbn; split.
  - assert (He_after : evaluation tf after fr (tail value)).
    { apply evaluation_get with target.
      - eapply (@evaluation_view tf middle after); [exact Hv|exact He].
      - right; exact (@complete_get_observed st fr target next next_fr value Hwrite). }
    eapply evaluation_frame; [symmetry; exact Howner|symmetry; exact Hlocal|symmetry; exact Htargets|exact He_after].
  - eapply (@continuation_view tf middle after); [exact Hv|exact Hk].
Qed.
Lemma get_resume_preserves tf roots st fr target tail k next next_fr value :
  R.complete_get st fr target = (next,next_fr,value) -> ranked st target ->
  ready (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) target ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  invariant tf roots (configuration next (R.RunRhs next_fr (tail value) k)).
Proof. exact (@complete_get_cursor_preserves tf roots st false fr target tail k next next_fr value). Qed.
Lemma return_get_preserves tf roots st fr target tail k next next_fr value :
  R.complete_get st fr target = (next,next_fr,value) -> ranked st target ->
  invariant tf roots (configuration st (R.Return (R.KAfterGet fr target tail k))) ->
  invariant tf roots (configuration next (R.RunRhs next_fr (tail value) k)).
Proof.
  intros Hwrite Hrank Hinv; eapply (@complete_get_cursor_preserves tf roots st true fr target tail k next next_fr value);
    [exact Hwrite|exact Hrank| |exact Hinv].
  exact (proj1 (proj2 (inv_control Hinv))).
Qed.
Lemma is_dormant_lookup st target : R.is_dormant st target = true -> R.semantic_lookup st target = Some D.bottom.
Proof.
  unfold R.is_dormant; rewrite andb_true_iff; intros [Hd H]; apply andb_true_iff in H as [Hsigma _].
  unfold R.semantic_lookup; destruct (M.lookup (R.sigma st) target); [discriminate|now rewrite Hd].
Qed.
Lemma unmaterialized_lookup st target : R.is_materialized st target = false -> M.lookup (R.sigma st) target = None.
Proof. unfold R.is_materialized; destruct (M.lookup (R.sigma st) target); [discriminate|reflexivity]. Qed.
Lemma remembered_lookup st target : M.lookup (R.sigma st) target = None ->
  R.semantic_lookup (R.remember_dormant st target) target = Some D.bottom.
Proof.
  intro H; unfold R.semantic_lookup, R.remember_dormant; cbn; rewrite H.
  assert (S.mem target (S.add target (R.dormant_bottom st)) = true) by (apply SL.add_spec; now left).
  now rewrite H0.
Qed.
Lemma dormant_get_preserves tf roots st fr target tail k : R.semantic_lookup st target = Some D.bottom ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  invariant tf roots (configuration (R.add_reader st target (R.frame_owner fr)) (R.RunRhs fr (tail D.bottom) k)).
Proof.
  intros Hlookup Hinv; assert (Howner : ranked st (R.frame_owner fr)).
  { pose proof (shape_stack_ranks (inv_shape Hinv)) as H; change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in H;
      now inversion H. }
  pose proof (@reader_state_preserves tf roots st (R.RunRhs fr (Syntax.Get target tail) k)
    target (R.frame_owner fr) Howner Hinv) as Hupdated.
  set (middle := configuration (R.add_reader st target (R.frame_owner fr)) (R.RunRhs fr (Syntax.Get target tail) k)) in Hupdated.
  set (after := configuration (R.add_reader st target (R.frame_owner fr)) (R.RunRhs fr (tail D.bottom) k)).
  assert (Hv : logical_view middle after) by (apply control_view; reflexivity).
  use_invariant_view Hupdated; [exact Hv|intros; exact I| |exact Hupdated].
  destruct (inv_control Hupdated) as [He Hk]; unfold after, configuration, control_valid; cbn; split.
  - apply evaluation_get with target.
    + eapply (@evaluation_view tf middle after); [exact Hv|exact He].
    + right; split; [exact Hlookup|apply reader_mem_add; now left].
  - eapply (@continuation_view tf middle after); [exact Hv|exact Hk].
Qed.

Lemma spawn_solved_preserves tf roots st fr target tail k : solved st target ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  invariant tf roots (configuration st (R.RunRhs fr tail k)).
Proof.
  intros Htarget Hinv; assert (Hv : logical_view (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k))
    (configuration st (R.RunRhs fr tail k))) by (apply control_view; reflexivity).
  use_invariant_view Hinv; [exact Hv|intros; exact I| |exact Hinv].
  destruct (inv_control Hinv) as [He Hk]; split.
  - apply evaluation_spawn with target.
    + eapply evaluation_view; [exact Hv|exact He].
    + left; left; exact Htarget.
  - eapply continuation_view; [exact Hv|exact Hk].
Qed.
Lemma spawn_child_preserves tf roots st fr target tail k : ranked st target ->
  R.rank_lt st (R.frame_owner fr) target = true ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  invariant tf roots (configuration st (R.StartEpisode target (R.KAfterSpawn fr tail k))).
Proof.
  intros Htarget Hgreater Hinv.
  pose proof (shape_stack_ranks (inv_shape Hinv)) as Hr;
    change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in Hr; inversion Hr; subst.
  assert (Howner : ranked st (R.frame_owner fr)) by assumption.
  apply (proj1 (compare_rank Howner Htarget)) in Hgreater.
  eapply (@push_child_preserves tf roots st (R.RunRhs fr (Syntax.Spawn target tail) k)
    target (R.KAfterSpawn fr tail k)); try reflexivity.
  - exact Htarget.
  - exact (@above_stack st (R.frame_owner fr) (suspended_owners k) target
      (shape_stack_order (inv_shape Hinv)) Hgreater).
  - pose proof (@push_history st (R.RunRhs fr (Syntax.Spawn target tail) k) target
      (R.KAfterSpawn fr tail k) eq_refl eq_refl eq_refl) as Hhistory.
    destruct (inv_control Hinv) as [He Hk]; split.
    + apply evaluation_spawn with target.
      * eapply (@evaluation_transport tf _ _ None); [exact Hhistory|discriminate|exact He].
      * left; right; left; right; now left.
    + eapply (@continuation_transport tf _ _ None); [exact Hhistory|discriminate|exact Hk].
  - exact Hinv.
Qed.
Lemma spawn_queued_preserves tf roots st fr target tail k : ranked st target ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  invariant tf roots (configuration (R.materialize (R.enqueue st target) target) (R.RunRhs fr tail k)).
Proof.
  intros Htarget Hinv; apply (@spawn_solved_preserves tf roots (R.materialize (R.enqueue st target) target) fr target tail k);
    [apply materialize_solves|].
  apply materialize_state_preserves; [exact Htarget| |now apply enqueue_state_preserves].
  right; left; apply queue_pending.
Qed.
Lemma get_queued_preserves tf roots st fr target tail k next next_fr value : ranked st target ->
  R.complete_get (R.enqueue st target) fr target = (next,next_fr,value) ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  invariant tf roots (configuration next (R.RunRhs next_fr (tail value) k)).
Proof.
  intros Htarget Hwrite Hinv; eapply (@get_resume_preserves tf roots (R.enqueue st target) fr target tail k next next_fr value).
  - exact Hwrite.
  - exact Htarget.
  - right; left; apply queue_pending.
  - now apply enqueue_state_preserves.
Qed.
Lemma restart_preserves tf roots st fr k remaining : R.queue st = R.frame_owner fr :: remaining ->
  invariant tf roots (configuration st (R.RunDrain fr k)) ->
  invariant tf roots (configuration (R.clear_side_dirty (R.with_queue st remaining) (R.frame_owner fr))
    (R.RunRhs (R.fresh_frame (R.clear_side_dirty (R.with_queue st remaining) (R.frame_owner fr))
      (R.frame_owner fr) (R.frame_phase fr)) (tf (R.frame_owner fr)) k)).
Proof.
  intros Hqueue Hinv; set (prepared := R.clear_side_dirty (R.with_queue st remaining) (R.frame_owner fr)).
  set (before := configuration st (R.RunDrain fr k)) in *;
    set (after := configuration prepared (R.RunRhs (R.fresh_frame prepared (R.frame_owner fr) (R.frame_phase fr))
      (tf (R.frame_owner fr)) k)).
  assert (Hbusy : forall x, busy before x -> busy after x).
  { intros x [[Hq|Hw]|Ha]; [|left; now right|now right].
    change (In x (R.queue st)) in Hq; rewrite Hqueue in Hq; destruct Hq as [E|Hq]; [subst x; right; now left|left; now left]. }
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [split; reflexivity|intros; right; left; now apply Hbusy|intros; right; now right]. }
  assert (Hhistory : history_transport before after (Some (R.frame_owner fr))).
  { apply transport_unchanged; try reflexivity.
    - intros x Hneq [Hq|Hw]; [|now right].
      change (In x (R.queue st)) in Hq; rewrite Hqueue in Hq; destruct Hq as [E|Hq]; [congruence|now left].
    - apply spawn_transport; [exact Hdem|intros; assumption].
    - intros x [Hs|Hb]; [now left|right; now apply Hbusy].
    - intros x _ H; exact H. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol].
  destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor.
  - constructor; try assumption.
    + change (ranked_list st remaining); change (ranked_list st (R.queue st)) in Hqr; rewrite Hqueue in Hqr; now inversion Hqr.
    + change (sorted_queue st remaining); change (sorted_queue st (R.queue st)) in Hqo; rewrite Hqueue in Hqo; now inversion Hqo.
    + exact I.
  - intros x Hsolved; destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq].
    + left; right; now left.
    + destruct (Hsummary x Hsolved) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
      right; exists result; eapply (@saved_transport tf before after (Some (R.frame_owner fr)));
        [exact Hhistory|congruence|exact Hsaved].
  - intros x; destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|now right].
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - unfold after, configuration, control_valid; cbn; split; [apply fresh_evaluation|].
    destruct Hcontrol as [_ Hk]; eapply (@continuation_transport tf before after (Some (R.frame_owner fr)) k);
      [exact Hhistory| |exact Hk].
    intros x H Heq; inversion Heq; subst; exact (@stack_owner_not_suspended st (R.frame_owner fr) k Hao H).
Qed.

Lemma pop_busy st ctrl child tail k : R.queue st = child :: tail ->
  active_owners ctrl = suspended_owners k ->
  forall x, busy (configuration st ctrl) x ->
    busy (configuration (R.with_queue st tail) (R.StartEpisode child k)) x.
Proof.
  intros Hqueue Ha x [[Hq|Hw]|Hactive]; [|left; now right|right; right; now rewrite <- Ha].
  change (In x (R.queue st)) in Hq; rewrite Hqueue in Hq; destruct Hq as [E|Hq];
    [subst x; right; now left|left; now left].
Qed.
Lemma pop_history st ctrl child tail k : R.queue st = child :: tail ->
  active_owners ctrl = suspended_owners k -> framed_owners ctrl = suspended_owners k -> seed_owners ctrl = suspended_seeds k ->
  history_transport (configuration st ctrl) (configuration (R.with_queue st tail) (R.StartEpisode child k)) (Some child).
Proof.
  intros Hqueue Ha Hf Hs; apply transport_unchanged; try reflexivity.
  - intros x Hneq [Hq|Hw]; [|now right].
    change (In x (R.queue st)) in Hq; rewrite Hqueue in Hq; destruct Hq as [E|Hq]; [congruence|now left].
  - apply spawn_transport; [|intros; assumption]; apply demand_same_store; [split; reflexivity| |].
    + intros x H; right; left; exact (@pop_busy st ctrl child tail k Hqueue Ha x H).
    + intros x H; right; right; change (In x (suspended_seeds k)); now rewrite <- Hs.
  - intros x [Hs0|Hb]; [now left|right; exact (@pop_busy st ctrl child tail k Hqueue Ha x Hb)].
  - intros x _ H; change (In x (framed_owners ctrl)); now rewrite Hf.
Qed.
Lemma popped_child_preserves tf roots st ctrl child tail k : R.queue st = child :: tail ->
  active_owners ctrl = suspended_owners k -> framed_owners ctrl = suspended_owners k ->
  seed_owners ctrl = suspended_seeds k ->
  (forall owner, In owner (suspended_owners k) -> priority st owner < priority st child) ->
  continuation_valid tf (configuration (R.with_queue st tail) (R.StartEpisode child k)) k ->
  invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (R.with_queue st tail) (R.StartEpisode child k)).
Proof.
  intros Hqueue Ha Hf Hs Habove Hkont Hinv; set (before := configuration st ctrl) in *;
    set (after := configuration (R.with_queue st tail) (R.StartEpisode child k)).
  pose proof (@pop_busy st ctrl child tail k Hqueue Ha) as Hbusy.
  pose proof (@pop_history st ctrl child tail k Hqueue Ha Hf Hs) as Hhistory.
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [split; reflexivity|intros; right; left; now apply Hbusy|].
    intros x H; right; right; change (In x (suspended_seeds k)); now rewrite <- Hs. }
  destruct Hinv as [Hshape Hsummary Hbounds Hreq Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor; try assumption.
    + change (ranked_list st tail); change (ranked_list st (R.queue st)) in Hqr; rewrite Hqueue in Hqr; now inversion Hqr.
    + change (sorted_queue st tail); change (sorted_queue st (R.queue st)) in Hqo; rewrite Hqueue in Hqo; now inversion Hqo.
    + change (ranked_list st (child :: suspended_owners k)); constructor.
      * change (ranked_list st (R.queue st)) in Hqr; rewrite Hqueue in Hqr; now inversion Hqr.
      * change (ranked_list st (active_owners ctrl)) in Har; now rewrite <- Ha.
    + change (sorted_queue st (child :: suspended_owners k)); constructor.
      * change (sorted_queue st (active_owners ctrl)) in Hao; now rewrite <- Ha.
      * apply Forall_forall; exact Habove.
    + intros x H; apply Hframes; change (In x (framed_owners ctrl)); now rewrite Hf.
    + exact I.
  - intros x Hsolved; destruct (V.eq_dec x child) as [->|Hneq]; [left; right; now left|].
    destruct (Hsummary x Hsolved) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
    right; exists result; eapply (@saved_transport tf before after (Some child)); [exact Hhistory|congruence|exact Hsaved].
  - intros x; destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|now right].
  - eapply (@requests_transport before after); [exact Hdem|reflexivity|intros; now left|exact Hreq].
  - exact (seeds_transport Hdem Hroots).
  - exact Hkont.
Qed.
Lemma drain_child_preserves tf roots st fr k child tail : R.queue st = child :: tail ->
  R.rank_lt st (R.frame_owner fr) child = true ->
  invariant tf roots (configuration st (R.RunDrain fr k)) ->
  invariant tf roots (configuration (R.with_queue st tail) (R.StartEpisode child (R.KDrain fr k))).
Proof.
  intros Hqueue Hgreater Hinv.
  pose proof (shape_stack_ranks (inv_shape Hinv)) as Hs;
    change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in Hs; inversion Hs; subst.
  pose proof (shape_queue_ranks (inv_shape Hinv)) as Hq;
    change (ranked_list st (R.queue st)) in Hq; rewrite Hqueue in Hq; inversion Hq; subst.
  assert (Howner : ranked st (R.frame_owner fr)) by assumption.
  assert (Hchild : ranked st child) by assumption.
  apply (proj1 (compare_rank Howner Hchild)) in Hgreater.
  assert (Habove : forall owner, In owner (R.frame_owner fr :: suspended_owners k) -> priority st owner < priority st child).
  { exact (@above_stack st (R.frame_owner fr) (suspended_owners k) child (shape_stack_order (inv_shape Hinv)) Hgreater). }
  eapply (@popped_child_preserves tf roots st (R.RunDrain fr k) child tail (R.KDrain fr k)); try reflexivity.
  - exact Hqueue.
  - exact Habove.
  - set (before := configuration st (R.RunDrain fr k));
      set (after := configuration (R.with_queue st tail) (R.StartEpisode child (R.KDrain fr k))).
    pose proof (@pop_history st (R.RunDrain fr k) child tail (R.KDrain fr k) Hqueue eq_refl eq_refl eq_refl) as Hhistory.
    destruct (inv_control Hinv) as [[result [Hsaved Hbound]] Hk]; split; [exists result; split|].
    + eapply (@saved_transport tf before after (Some child)); [exact Hhistory| |exact Hsaved].
      intro E; inversion E; subst; lia.
    + eapply (@transport_incoming before after (Some child)); [exact Hhistory| |exact Hbound].
      intro E; inversion E; subst; lia.
    + eapply (@continuation_transport tf before after (Some child) k); [exact Hhistory| |exact Hk].
      intros x Hin E; pose proof (Habove x (or_intror Hin)); inversion E; subst; lia.
  - exact Hinv.
Qed.

Lemma shape_side_write tf st ctrl fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  machine_shape tf (configuration st ctrl) -> machine_shape tf (configuration next ctrl).
Proof.
  intros Hwrite Hshape; destruct (@side_write_metadata st fr target input next changed Hwrite)
    as [Hsigma [Hrank [Hreader [Hdormant [Hqueue [Hwake [Hfifo Hrequested]]]]]]].
  destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor.
  - change (RankLaws.valid (R.ranking next)); now rewrite Hrank.
  - intros x H; unfold ranked; change (exists n, Ranks.lookup (R.ranking next) x = Some n); rewrite Hrank.
    apply Hlive; change (R.is_materialized next x = true) in H;
      unfold R.is_materialized in H; now rewrite Hsigma in H.
  - intros x H; apply Hd; change (S.mem x (R.dormant_bottom next) = true) in H; now rewrite Hdormant in H.
  - intros target0 owner H; unfold ranked; change (exists n, Ranks.lookup (R.ranking next) owner = Some n); rewrite Hrank.
    apply Hr with target0; change (S.mem owner (R.lookup_set (R.readers next) target0) = true) in H; now rewrite Hreader in H.
  - unfold ranked_list, ranked; change (Forall (fun x => exists n, Ranks.lookup (R.ranking next) x = Some n) (R.queue next));
      now rewrite Hrank, Hqueue.
  - unfold ranked_list, ranked; change (Forall (fun x => exists n, Ranks.lookup (R.ranking next) x = Some n) (R.deferred_wakes next));
      now rewrite Hrank, Hwake.
  - unfold sorted_queue, priority, configuration; cbn; now rewrite Hrank, Hqueue.
  - unfold sorted_queue, priority, configuration; cbn; now rewrite Hrank, Hwake.
  - unfold ranked_list, ranked, configuration; cbn; now rewrite Hrank.
  - unfold sorted_queue, priority, configuration; cbn; now rewrite Hrank.
  - intros x H; apply (proj2 (solved_view x (conj Hsigma Hdormant))); exact (Hframes x H).
  - unfold wakes_finished, configuration in *; cbn in *; destruct ctrl; cbn in *; trivial; now rewrite Hwake.
Qed.
Lemma continue_side_fields st fr target body k change :
  let after := R.cfg_state (R.continue_side st fr target body k change) in
  R.sigma after = R.sigma st /\ R.ranking after = R.ranking st /\ R.readers after = R.readers st /\
  R.contributions after = R.contributions st /\ R.dormant_bottom after = R.dormant_bottom st /\
  R.deferred_wakes after = R.deferred_wakes st /\ R.pending_spawns after = R.pending_spawns st /\
  R.requested_spawns after = R.requested_spawns st.
Proof.
  unfold R.continue_side; destruct change; [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|];
    repeat split; reflexivity.
Qed.
Lemma continue_side_footprints st fr target body k change :
  framed_owners (R.cfg_control (R.continue_side st fr target body k change)) = R.frame_owner fr :: suspended_owners k /\
  seed_owners (R.cfg_control (R.continue_side st fr target body k change)) = suspended_seeds k /\
  (forall owner, In owner (R.frame_owner fr :: suspended_owners k) ->
    In owner (active_owners (R.cfg_control (R.continue_side st fr target body k change)))).
Proof.
  unfold R.continue_side; destruct change; [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|];
    idtac.
  all: cbn; split; [reflexivity|]; split; [reflexivity|]; intros; assumption || (right; assumption).
Qed.
Lemma continue_side_pending st fr target body k change owner : pending st owner ->
  pending (R.cfg_state (R.continue_side st fr target body k change)) owner.
Proof.
  unfold R.continue_side; destruct change; [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|];
    idtac.
  all: intro H; first [exact H|exact (@queue_preserves_pending st target owner H)].
Qed.
Lemma continue_side_target_busy st fr target body k : busy (R.continue_side st fr target body k true) target.
Proof.
  unfold R.continue_side; destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target));
    [right; now left|left; apply queue_pending].
Qed.
Lemma shape_continue_side tf st fr old_body target body k change : ranked st target ->
  machine_shape tf (configuration st (R.RunRhs fr old_body k)) ->
  machine_shape tf (R.continue_side st fr target body k change).
Proof.
  intros Htarget Hshape; unfold R.continue_side; destruct change.
  - destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target)) eqn:Hchild.
    + apply andb_true_iff in Hchild as [Hgreater _].
      destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw].
      assert (Howner : ranked st (R.frame_owner fr)) by (change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in Har; now inversion Har).
      apply (proj1 (compare_rank Howner Htarget)) in Hgreater.
      constructor; try assumption.
      * constructor; [exact Htarget|exact Har].
      * constructor; [exact Hao|]; apply Forall_forall.
        exact (@above_stack st (R.frame_owner fr) (suspended_owners k) target Hao Hgreater).
    + destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor; try assumption.
      * apply Forall_forall; intros x H; apply queue_insert_members in H as [->|H]; [exact Htarget|].
        exact (proj1 (Forall_forall _ _) Hqr x H).
      * change (sorted_queue st (R.queue_insert (R.ranking st) target (R.queue st))); now apply queue_insert_sorted.
  - destruct Hshape; constructor; assumption.
Qed.
Lemma continue_side_target_incoming tf st fr target body k : ranked st target ->
  machine_shape tf (configuration st (R.RunRhs fr body k)) ->
  incoming_bound (R.continue_side st fr target body k true) target.
Proof.
  intros Htarget Hshape; unfold R.continue_side;
    destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target)) eqn:Hchild.
  - right; left; intro Hin; apply andb_true_iff in Hchild as [Hgreater _].
    pose proof (shape_stack_ranks Hshape) as Hr;
      change (ranked_list st (R.frame_owner fr :: suspended_owners k)) in Hr; inversion Hr; subst.
    assert (Howner : ranked st (R.frame_owner fr)) by assumption.
    apply (proj1 (compare_rank Howner Htarget)) in Hgreater.
    pose proof (@above_stack st (R.frame_owner fr) (suspended_owners k) target (shape_stack_order Hshape) Hgreater target Hin); lia.
  - left; apply queue_pending.
Qed.

Lemma shape_rhs_owner tf st fr next_fr body next_body k : R.frame_owner next_fr = R.frame_owner fr ->
  machine_shape tf (configuration st (R.RunRhs fr body k)) ->
  machine_shape tf (configuration st (R.RunRhs next_fr next_body k)).
Proof.
  intros Howner Hshape; destruct Hshape as [Hv Hlive Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw]; constructor; try assumption.
  - change (ranked_list st (R.frame_owner next_fr :: suspended_owners k)); now rewrite Howner.
  - change (sorted_queue st (R.frame_owner next_fr :: suspended_owners k)); now rewrite Howner.
  - intros x H; apply Hframes; change (In x (R.frame_owner fr :: suspended_owners k));
      change (In x (R.frame_owner next_fr :: suspended_owners k)) in H; now rewrite Howner in H.
Qed.
Lemma side_progress_preserves tf roots st fr target raw tail k next changed chosen :
  R.write_side_contribution st (R.with_frame_side fr target (R.accumulated_side_input fr target raw))
    target (R.accumulated_side_input fr target raw) = (next,changed) ->
  (chosen = false -> changed = false) -> ranked st target ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) ->
  invariant tf roots (R.continue_side next
    (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) target tail k chosen).
Proof.
  intros Hwrite Hchosen Htarget Hinv;
    set (fr1 := R.with_frame_side fr target (R.accumulated_side_input fr target raw)) in *.
  set (before := configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) in *;
    set (after := R.continue_side next fr1 target tail k chosen).
  destruct (@side_write_metadata st fr1 target (R.accumulated_side_input fr target raw) next changed Hwrite)
    as [Hsigma [Hrank [Hreader [Hdormant [Hqueue [Hwake [Hfifo Hrequested]]]]]]].
  destruct (@continue_side_fields next fr1 target tail k chosen)
    as [Hs [Hrk [Hr [Hcon [Hd [Hw [Hf Hreq]]]]]]].
  change (R.sigma (R.cfg_state after) = R.sigma next) in Hs;
    change (R.ranking (R.cfg_state after) = R.ranking next) in Hrk;
    change (R.readers (R.cfg_state after) = R.readers next) in Hr;
    change (R.contributions (R.cfg_state after) = R.contributions next) in Hcon;
    change (R.dormant_bottom (R.cfg_state after) = R.dormant_bottom next) in Hd;
    change (R.deferred_wakes (R.cfg_state after) = R.deferred_wakes next) in Hw;
    change (R.pending_spawns (R.cfg_state after) = R.pending_spawns next) in Hf;
    change (R.requested_spawns (R.cfg_state after) = R.requested_spawns next) in Hreq.
  destruct (@continue_side_footprints next fr1 target tail k chosen) as [Hframes [Hseeds Hactive]].
  change (framed_owners (R.cfg_control after) = R.frame_owner fr :: suspended_owners k) in Hframes;
    change (seed_owners (R.cfg_control after) = suspended_seeds k) in Hseeds.
  assert (Hstore : store_view (R.cfg_state after) st) by (split; [now rewrite Hs,Hsigma|now rewrite Hd,Hdormant]).
  assert (Hpending : forall x, pending st x -> pending (R.cfg_state after) x).
  { intros x H; apply (@continue_side_pending next fr1 target tail k chosen x).
    unfold pending; now rewrite Hqueue,Hwake. }
  assert (Hbusy : forall x, busy before x -> busy after x).
  { intros x [H|H]; [left; now apply Hpending|right; now apply Hactive]. }
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [exact Hstore|intros; right; left; now apply Hbusy|].
    intros x H; right; right; now rewrite Hseeds. }
  assert (Hspawns : forall x, spawn_accounted before x -> spawn_accounted after x).
  { apply spawn_transport; [exact Hdem|intros x H; now rewrite Hreq,Hrequested]. }
  assert (Hreads : forall owner key value, read_guard st owner key value -> read_guard (R.cfg_state after) owner key value).
  { intros owner key value; apply read_guard_monotone; [exact (Hpending owner)| |].
    - exact (@lookup_view (R.cfg_state after) st key Hstore).
    - intros H; now rewrite Hr,Hreader. }
  assert (Hvalue : forall x, R.sigma_value (R.cfg_state after) x = R.sigma_value st x).
  { intro x; unfold R.sigma_value; now rewrite Hs,Hsigma. }
  assert (Hother_aggregate : forall x, x <> target -> R.aggregate (R.cfg_state after) x = R.aggregate st x).
  { intros x Hneq; unfold R.aggregate; rewrite Hcon;
      exact (@side_write_other_aggregate st fr1 target (R.accumulated_side_input fr target raw) next changed Hwrite x Hneq). }
  assert (Htarget_next : ranked next target) by (unfold ranked in *; now rewrite Hrank).
  assert (Hshape_next : machine_shape tf (configuration next (R.RunRhs fr1 tail k))).
  { eapply (@shape_rhs_owner tf next fr fr1 (Syntax.Side target raw tail) tail k); [reflexivity|].
    eapply (@shape_side_write tf st (R.RunRhs fr (Syntax.Side target raw tail) k) fr1 target
      (R.accumulated_side_input fr target raw) next changed); [exact Hwrite|exact (inv_shape Hinv)]. }
  assert (Hincoming : forall x, incoming_bound before x -> incoming_bound after x).
  { intros x [Hp|[Hnot|Hb]]; [left; now apply Hpending|right; left; intro H; apply Hnot; now rewrite Hframes in H|].
    destruct (V.eq_dec x target) as [->|Hneq].
    - destruct chosen.
      + exact (@continue_side_target_incoming tf next fr1 target tail k Htarget_next Hshape_next).
      + right; right; rewrite Hvalue; unfold R.aggregate; rewrite Hcon.
        specialize (Hchosen eq_refl); subst changed.
        destruct (@side_write_unchanged_aggregate st fr1 target (R.accumulated_side_input fr target raw) next Hwrite) as [Hle _].
        eapply DL.leq_trans; [exact Hle|exact Hb].
    - right; right; rewrite Hvalue, Hother_aggregate by assumption; exact Hb. }
  assert (Hhistory : history_transport before after (Some (R.frame_owner fr))).
  { constructor.
    - intros owner key value _ H; now apply Hreads.
    - intros owner key Hneq; unfold R.stored_contribution; rewrite Hcon.
      change (D.leq (R.stored_contribution st owner key) (R.stored_contribution next owner key) = true).
      rewrite (@side_write_other_source st fr1 target (R.accumulated_side_input fr target raw) next changed Hwrite owner key)
        by (unfold fr1; cbn; congruence); apply DL.leq_refl.
    - intros x _; rewrite Hvalue; apply DL.leq_refl.
    - intros x _ H; now apply Hincoming.
    - exact Hspawns.
    - intros x [Hs0|Hb]; [left; apply (proj2 (solved_view x Hstore)); exact Hs0|right; now apply Hbusy]. }
  destruct Hinv as [Hshape Hsummary Hbounds Hrequests Hroots [He Hk]]; constructor.
  - apply (@shape_continue_side tf next fr1 tail target tail k chosen); [exact Htarget_next|exact Hshape_next].
  - intros x Hsolved; apply (proj1 (solved_view x Hstore)) in Hsolved.
    destruct (V.eq_dec x (R.frame_owner fr)) as [E|Hneq].
    + left; right; apply Hactive; change (In x (R.frame_owner fr :: suspended_owners k)); now left.
    + destruct (Hsummary x Hsolved) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
      right; exists result; eapply (@saved_transport tf before after (Some (R.frame_owner fr)));
        [exact Hhistory|congruence|exact Hsaved].
  - intros x; destruct (V.eq_dec x target) as [->|Hneq].
    + destruct chosen.
      * left; exact (@continue_side_target_busy next fr1 target tail k).
      * destruct (Hbounds target) as [Hb|Hb]; [left; now apply Hbusy|right].
        rewrite Hvalue; unfold R.aggregate; rewrite Hcon; specialize (Hchosen eq_refl); subst changed.
        destruct (@side_write_unchanged_aggregate st fr1 target (R.accumulated_side_input fr target raw) next Hwrite) as [Hle _].
        eapply DL.leq_trans; [exact Hle|exact Hb].
    + destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|right].
      rewrite Hvalue,Hother_aggregate by assumption; exact Hb.
  - eapply (@requests_transport before after); [exact Hdem|now rewrite Hreq,Hrequested| |exact Hrequests].
    intros x H; left; now rewrite Hf,Hfifo.
  - exact (seeds_transport Hdem Hroots).
  - assert (He_after : evaluation tf after fr1 tail).
    { destruct He as [reads [sides [spawns [Hp [Hr0 [Hl [Hpub [Htargets Hspawn]]]]]]]].
      exists reads, (sides ++ [(target,raw)]), spawns; split.
      - apply PrefixSide; exact Hp.
      - split; [intros x v H; apply Hreads; exact (Hr0 x v H)|]; split.
        + exact (@local_covers_side fr sides target raw Hl).
        + split.
          * intros key H; unfold R.stored_contribution; rewrite Hcon.
            exact (@side_write_local_publish st fr target raw next changed Hpub Hwrite key H).
          * split; [exact (@side_targets_side fr sides target (R.accumulated_side_input fr target raw) raw Htargets)|].
            intros x H; apply Hspawns; exact (Hspawn x H). }
    assert (Hk_after : continuation_valid tf after k).
    { eapply (@continuation_transport tf before after (Some (R.frame_owner fr)) k); [exact Hhistory| |exact Hk].
      intros x H E; pose proof (@stack_owner_not_suspended st (R.frame_owner fr) k (shape_stack_order Hshape)) as Hnot;
        inversion E; subst; now apply Hnot. }
    unfold after, R.continue_side in He_after, Hk_after |- *; unfold control_valid; destruct chosen;
      [destruct (R.rank_lt next (R.frame_owner fr1) target && negb (R.is_materialized next target))|];
      cbn [R.cfg_control continuation_valid]; split; assumption.
Qed.

Lemma dead_publication_preserves tf roots st fr target direct k next changed :
  R.write_side_contribution st fr target D.bottom = (next,changed) ->
  S.mem target (R.frame_current_targets fr) = false -> ranked st target ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Ret direct) k)) ->
  invariant tf roots (R.continue_side next fr target (Syntax.Ret direct) k changed).
Proof.
  intros Hwrite Hdead Htarget Hinv.
  set (before := configuration st (R.RunRhs fr (Syntax.Ret direct) k)) in *;
    set (after := R.continue_side next fr target (Syntax.Ret direct) k changed).
  destruct (@side_write_metadata st fr target D.bottom next changed Hwrite)
    as [Hsigma [Hrank [Hreader [Hdormant [Hqueue [Hwake [Hfifo Hrequested]]]]]]].
  destruct (@continue_side_fields next fr target (Syntax.Ret direct) k changed)
    as [Hs [Hrk [Hr [Hcon [Hd [Hw [Hf Hreq]]]]]]].
  change (R.sigma (R.cfg_state after) = R.sigma next) in Hs;
    change (R.ranking (R.cfg_state after) = R.ranking next) in Hrk;
    change (R.readers (R.cfg_state after) = R.readers next) in Hr;
    change (R.contributions (R.cfg_state after) = R.contributions next) in Hcon;
    change (R.dormant_bottom (R.cfg_state after) = R.dormant_bottom next) in Hd;
    change (R.deferred_wakes (R.cfg_state after) = R.deferred_wakes next) in Hw;
    change (R.pending_spawns (R.cfg_state after) = R.pending_spawns next) in Hf;
    change (R.requested_spawns (R.cfg_state after) = R.requested_spawns next) in Hreq.
  destruct (@continue_side_footprints next fr target (Syntax.Ret direct) k changed) as [Hframes [Hseeds Hactive]].
  change (framed_owners (R.cfg_control after) = R.frame_owner fr :: suspended_owners k) in Hframes;
    change (seed_owners (R.cfg_control after) = suspended_seeds k) in Hseeds.
  assert (Hstore : store_view (R.cfg_state after) st) by (split; [now rewrite Hs,Hsigma|now rewrite Hd,Hdormant]).
  assert (Hpending : forall x, pending st x -> pending (R.cfg_state after) x).
  { intros x H; apply (@continue_side_pending next fr target (Syntax.Ret direct) k changed x).
    unfold pending; now rewrite Hqueue,Hwake. }
  assert (Hbusy : forall x, busy before x -> busy after x).
  { intros x [H|H]; [left; now apply Hpending|right; now apply Hactive]. }
  assert (Hdem : demand_transport before after).
  { apply demand_same_store; [exact Hstore|intros; right; left; now apply Hbusy|].
    intros x H; right; right; now rewrite Hseeds. }
  assert (Hspawns : forall x, spawn_accounted before x -> spawn_accounted after x).
  { apply spawn_transport; [exact Hdem|intros x H; now rewrite Hreq,Hrequested]. }
  assert (Hreads : forall owner key value, read_guard st owner key value -> read_guard (R.cfg_state after) owner key value).
  { intros owner key value; apply read_guard_monotone; [exact (Hpending owner)| |].
    - exact (@lookup_view (R.cfg_state after) st key Hstore).
    - intros H; now rewrite Hr,Hreader. }
  assert (Hvalue : forall x, R.sigma_value (R.cfg_state after) x = R.sigma_value st x).
  { intro x; unfold R.sigma_value; now rewrite Hs,Hsigma. }
  assert (Hother_aggregate : forall x, x <> target -> R.aggregate (R.cfg_state after) x = R.aggregate st x).
  { intros x Hneq; unfold R.aggregate; rewrite Hcon;
      exact (@side_write_other_aggregate st fr target D.bottom next changed Hwrite x Hneq). }
  assert (Htarget_next : ranked next target) by (unfold ranked in *; now rewrite Hrank).
  assert (Hshape_next : machine_shape tf (configuration next (R.RunRhs fr (Syntax.Ret direct) k))).
  { eapply (@shape_side_write tf st (R.RunRhs fr (Syntax.Ret direct) k) fr target
      D.bottom next changed); [exact Hwrite|exact (inv_shape Hinv)]. }
  assert (Hincoming : forall x, incoming_bound before x -> incoming_bound after x).
  { intros x [Hp|[Hnot|Hb]]; [left; now apply Hpending|right; left; intro H; apply Hnot; now rewrite Hframes in H|].
    destruct (V.eq_dec x target) as [->|Hneq].
    - destruct changed.
      + exact (@continue_side_target_incoming tf next fr target (Syntax.Ret direct) k Htarget_next Hshape_next).
      + right; right; rewrite Hvalue; unfold R.aggregate; rewrite Hcon.

        destruct (@side_write_unchanged_aggregate st fr target D.bottom next Hwrite) as [Hle _].
        eapply DL.leq_trans; [exact Hle|exact Hb].
    - right; right; rewrite Hvalue, Hother_aggregate by assumption; exact Hb. }
  assert (Hhistory : history_transport before after (Some (R.frame_owner fr))).
  { constructor.
    - intros owner key value _ H; now apply Hreads.
    - intros owner key Hneq; unfold R.stored_contribution; rewrite Hcon.
      change (D.leq (R.stored_contribution st owner key) (R.stored_contribution next owner key) = true).
      rewrite (@side_write_other_source st fr target D.bottom next changed Hwrite owner key)
        by congruence; apply DL.leq_refl.
    - intros x _; rewrite Hvalue; apply DL.leq_refl.
    - intros x _ H; now apply Hincoming.
    - exact Hspawns.
    - intros x [Hs0|Hb]; [left; apply (proj2 (solved_view x Hstore)); exact Hs0|right; now apply Hbusy]. }
  destruct Hinv as [Hshape Hsummary Hbounds Hrequests Hroots [He Hk]]; constructor.
  - apply (@shape_continue_side tf next fr (Syntax.Ret direct) target (Syntax.Ret direct) k changed); [exact Htarget_next|exact Hshape_next].
  - intros x Hsolved; apply (proj1 (solved_view x Hstore)) in Hsolved.
    destruct (V.eq_dec x (R.frame_owner fr)) as [E|Hneq].
    + left; right; apply Hactive; change (In x (R.frame_owner fr :: suspended_owners k)); now left.
    + destruct (Hsummary x Hsolved) as [Hb|[result Hsaved]]; [left; now apply Hbusy|].
      right; exists result; eapply (@saved_transport tf before after (Some (R.frame_owner fr)));
        [exact Hhistory|congruence|exact Hsaved].
  - intros x; destruct (V.eq_dec x target) as [->|Hneq].
    + destruct changed.
      * left; exact (@continue_side_target_busy next fr target (Syntax.Ret direct) k).
      * destruct (Hbounds target) as [Hb|Hb]; [left; now apply Hbusy|right].
        rewrite Hvalue; unfold R.aggregate; rewrite Hcon;
        destruct (@side_write_unchanged_aggregate st fr target D.bottom next Hwrite) as [Hle _].
        eapply DL.leq_trans; [exact Hle|exact Hb].
    + destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|right].
      rewrite Hvalue,Hother_aggregate by assumption; exact Hb.
  - eapply (@requests_transport before after); [exact Hdem|now rewrite Hreq,Hrequested| |exact Hrequests].
    intros x H; left; now rewrite Hf,Hfifo.
  - exact (seeds_transport Hdem Hroots).
  - assert (He_after : evaluation tf after fr (Syntax.Ret direct)).
    { destruct He as [reads [sides [spawns [Hp [Hr0 [Hl [Hpub [Htargets Hspawn]]]]]]]].
      exists reads, sides, spawns; split; [exact Hp|]; split.
      - intros x v H; apply Hreads; exact (Hr0 x v H).
      - split; [exact Hl|]; split.
        + intros key H; assert (Hneq : key <> target) by (intro E; subst key; congruence).
          unfold R.stored_contribution; rewrite Hcon;
            rewrite (@side_write_other_target st fr target D.bottom next changed Hwrite key Hneq).
          exact (Hpub key H).
        + split; [exact Htargets|]; intros x H; apply Hspawns; exact (Hspawn x H). }
    assert (Hk_after : continuation_valid tf after k).
    { eapply (@continuation_transport tf before after (Some (R.frame_owner fr)) k); [exact Hhistory| |exact Hk].
      intros x H E; pose proof (@stack_owner_not_suspended st (R.frame_owner fr) k (shape_stack_order Hshape)) as Hnot;
        inversion E; subst; now apply Hnot. }
    unfold after, R.continue_side in He_after, Hk_after |- *; unfold control_valid; destruct changed;
      [destruct (R.rank_lt next (R.frame_owner fr) target && negb (R.is_materialized next target))|];
      cbn [R.cfg_control continuation_valid]; split; assumption.
Qed.

Lemma dirty_state_view st ctrl target :
  logical_view (configuration st ctrl) (configuration (R.mark_side_dirty st target) ctrl).
Proof. constructor; reflexivity. Qed.
Lemma continue_side_control tf st fr target body k changed :
  control_valid tf (R.continue_side st fr target body k changed) <->
  evaluation tf (R.continue_side st fr target body k changed) fr body /\
  continuation_valid tf (R.continue_side st fr target body k changed) k.
Proof.
  unfold R.continue_side; destruct changed;
    [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|]; reflexivity.
Qed.
Lemma dirty_side_view st fr target body k changed :
  logical_view (R.continue_side st fr target body k changed)
    (R.continue_side (R.mark_side_dirty st target) fr target body k changed).
Proof.
  unfold R.continue_side, R.mark_side_dirty, R.rank_lt, R.is_materialized; cbn;
    destruct changed; [destruct (R.ranking_lt (R.ranking st) (R.frame_owner fr) target &&
      negb (match M.lookup (R.sigma st) target with Some _ => true | None => false end))|];
    constructor; reflexivity.
Qed.
Lemma continue_side_wakes st fr target body k changed :
  wakes_finished (R.continue_side st fr target body k changed).
Proof.
  unfold R.continue_side; destruct changed;
    [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|]; exact I.
Qed.
Lemma dirty_side_preserves tf roots st fr target body k changed :
  invariant tf roots (R.continue_side st fr target body k changed) ->
  invariant tf roots (R.continue_side (R.mark_side_dirty st target) fr target body k changed).
Proof.
  intro H; pose proof (@dirty_side_view st fr target body k changed) as Hv.
  eapply (@invariant_view tf roots _ _ Hv); [| |exact H].
  - intros _; apply continue_side_wakes.
  - apply continue_side_control;
    destruct (proj1 (@continue_side_control tf st fr target body k changed) (inv_control H)) as [He Hk].
    split; [exact (@evaluation_view tf _ _ _ _ Hv He)|exact (@continuation_view tf _ _ _ Hv Hk)].
Qed.
Lemma rhs_dead_view st fr direct pending k :
  logical_view (configuration st (R.RunRhs fr (Syntax.Ret direct) k))
    (configuration st (R.RunDead fr direct pending k)).
Proof. constructor; reflexivity. Qed.
Lemma rhs_dead_preserves tf roots st fr direct pending k :
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Ret direct) k)) <->
  invariant tf roots (configuration st (R.RunDead fr direct pending k)).
Proof.
  split; intro H.
  - eapply (@invariant_view tf roots _ _ (rhs_dead_view st fr direct pending k));
      [exact (fun _ => I)| |exact H].
    destruct (inv_control H) as [He Hk]; split;
      [exact (@evaluation_view tf _ _ _ _ (rhs_dead_view st fr direct pending k) He)|
       exact (@continuation_view tf _ _ _ (rhs_dead_view st fr direct pending k) Hk)].
  - assert (Hv : logical_view (configuration st (R.RunDead fr direct pending k))
        (configuration st (R.RunRhs fr (Syntax.Ret direct) k))) by (constructor; reflexivity).
    eapply (@invariant_view tf roots _ _ Hv); [exact (fun _ => I)| |exact H].
    destruct (inv_control H) as [He Hk]; split;
      [exact (@evaluation_view tf _ _ _ _ Hv He)|exact (@continuation_view tf _ _ _ Hv Hk)].
Qed.
Lemma continue_dead_view st fr direct target pending k changed :
  logical_view (R.continue_side st fr target (Syntax.Ret direct) k changed)
    (R.continue_dead st fr direct target pending k changed).
Proof.
  unfold R.continue_side, R.continue_dead; destruct changed;
    [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|];
    constructor; reflexivity.
Qed.
Lemma continue_dead_control tf st fr direct target pending k changed :
  control_valid tf (R.continue_dead st fr direct target pending k changed) <->
  evaluation tf (R.continue_dead st fr direct target pending k changed) fr (Syntax.Ret direct) /\
  continuation_valid tf (R.continue_dead st fr direct target pending k changed) k.
Proof.
  unfold R.continue_dead; destruct changed;
    [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|]; reflexivity.
Qed.
Lemma continue_dead_preserves tf roots st fr direct target pending k changed :
  invariant tf roots (R.continue_side st fr target (Syntax.Ret direct) k changed) ->
  invariant tf roots (R.continue_dead st fr direct target pending k changed).
Proof.
  intro H; pose proof (@continue_dead_view st fr direct target pending k changed) as Hv.
  eapply (@invariant_view tf roots _ _ Hv); [| |exact H].
  - unfold R.continue_dead; destruct changed;
      [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|]; exact (fun _ => I).
  - apply continue_dead_control.
    destruct (proj1 (@continue_side_control tf st fr target (Syntax.Ret direct) k changed) (inv_control H)) as [He Hk].
    split; [exact (@evaluation_view tf _ _ _ _ Hv He)|exact (@continuation_view tf _ _ _ Hv Hk)].
Qed.
Lemma dead_progress_preserves tf roots st fr direct target pending k next changed :
  R.write_side_contribution st fr target D.bottom = (next,changed) ->
  S.mem target (R.frame_current_targets fr) = false -> ranked st target ->
  invariant tf roots (configuration st (R.RunDead fr direct (target :: pending) k)) ->
  invariant tf roots (R.continue_dead (if changed then R.mark_side_dirty next target else next)
    fr direct target pending k changed).
Proof.
  intros Hwrite Hdead Htarget Hinv; apply continue_dead_preserves.
  pose proof (proj2 (@rhs_dead_preserves tf roots st fr direct (target :: pending) k) Hinv) as Hrhs.
  pose proof (@dead_publication_preserves tf roots st fr target direct k next changed Hwrite Hdead Htarget Hrhs) as Hnext.
  destruct changed; [now apply dirty_side_preserves|exact Hnext].
Qed.

Lemma prefix_ret_empty direct body reads sides spawns :
  prefix (Syntax.Ret direct) body reads sides spawns ->
  body = Syntax.Ret direct /\ reads = [] /\ sides = [] /\ spawns = [].
Proof.
  intro H; remember (Syntax.Ret direct) as root eqn:E in H.
  induction H; subst; [repeat split; reflexivity| | |].
  all: destruct IHprefix as [Hbad _]; discriminate.
Qed.
Lemma evaluation_ret_transport tf before after owner direct fr body :
  tf owner = Syntax.Ret direct -> R.frame_owner fr = owner ->
  evaluation tf before fr body -> evaluation tf after fr body.
Proof.
  intros Hbody Howner [reads [sides [spawns [Hp [Hr [Hl [Hpub [Ht Hs]]]]]]]].
  rewrite Howner,Hbody in Hp; apply prefix_ret_empty in Hp as [-> [-> [-> ->]]].
  exists [],[],[]; split; [rewrite Howner,Hbody; constructor|]; split.
  - intros x v H; contradiction.
  - split; [intros x v H; contradiction|]; split.
    + intros x H; apply Ht in H as [v H]; contradiction.
    + split; [exact Ht|intros x H; contradiction].
Qed.
Lemma continuation_ret_transport tf before after owner direct k :
  history_transport before after (Some owner) -> tf owner = Syntax.Ret direct ->
  R.pure_bottom_rhs tf owner = true ->
  D.leq (R.aggregate (R.cfg_state after) owner) (R.sigma_value (R.cfg_state after) owner) = true ->
  continuation_valid tf before k -> continuation_valid tf after k.
Proof.
  intros Ht Hbody Hpure Hbound; induction k as [|seeds|fr target next k IHk|fr next k IHk|fr next k IHk|fr direct0 pending k IHk|fr k IHk]; cbn; intro H; try exact I.
  - destruct H as [He [Hr Hk]]; split.
    + destruct (V.eq_dec (R.frame_owner fr) owner) as [E|E].
      * exact (@evaluation_ret_transport tf before after owner direct fr _ Hbody E He).
      * eapply (@evaluation_transport tf before after (Some owner)); [exact Ht|congruence|exact He].
    + split; [exact (transport_ready Ht Hr)|now apply IHk].
  - destruct H as [He Hk]; split.
    + destruct (V.eq_dec (R.frame_owner fr) owner) as [E|E].
      * exact (@evaluation_ret_transport tf before after owner direct fr _ Hbody E He).
      * eapply (@evaluation_transport tf before after (Some owner)); [exact Ht|congruence|exact He].
    + now apply IHk.
  - destruct H as [He Hk]; split.
    + destruct (V.eq_dec (R.frame_owner fr) owner) as [E|E].
      * exact (@evaluation_ret_transport tf before after owner direct fr _ Hbody E He).
      * eapply (@evaluation_transport tf before after (Some owner)); [exact Ht|congruence|exact He].
    + now apply IHk.
  - destruct H as [He Hk]; split.
    + destruct (V.eq_dec (R.frame_owner fr) owner) as [E|E].
      * exact (@evaluation_ret_transport tf before after owner direct fr _ Hbody E He).
      * eapply (@evaluation_transport tf before after (Some owner)); [exact Ht|congruence|exact He].
    + now apply IHk.
  - destruct H as [Hcomplete Hk]; split; [|now apply IHk].
    destruct (V.eq_dec (R.frame_owner fr) owner) as [E|E].
    + destruct (@dormant_saved tf after owner Hpure) as [result Hr].
      exists result; rewrite E; split; [exact Hr|right; right; exact Hbound].
    + destruct Hcomplete as [result [Hr Hi]]; exists result; split.
      * eapply (@saved_transport tf before after (Some owner)); [exact Ht|congruence|exact Hr].
      * eapply (@transport_incoming before after (Some owner)); [exact Ht|congruence|exact Hi].
Qed.

Lemma control_ret_transport tf before after owner direct :
  R.cfg_control after = R.cfg_control before ->
  history_transport before after (Some owner) -> tf owner = Syntax.Ret direct ->
  R.pure_bottom_rhs tf owner = true ->
  D.leq (R.aggregate (R.cfg_state after) owner) (R.sigma_value (R.cfg_state after) owner) = true ->
  control_valid tf before -> control_valid tf after.
Proof.
  intros Hctrl Ht Hbody Hpure Hbound.
  assert (He : forall fr body, evaluation tf before fr body -> evaluation tf after fr body).
  { intros fr body H; destruct (V.eq_dec (R.frame_owner fr) owner) as [E|E].
    - exact (@evaluation_ret_transport tf before after owner direct fr body Hbody E H).
    - eapply (@evaluation_transport tf before after (Some owner)); [exact Ht|congruence|exact H]. }
  assert (Hk : forall k, continuation_valid tf before k -> continuation_valid tf after k).
  { intros k H; exact (@continuation_ret_transport tf before after owner direct k Ht Hbody Hpure Hbound H). }
  unfold control_valid; rewrite Hctrl; destruct (R.cfg_control before); cbn; try (tauto || exact (Hk _)).
  all: intros [Hframe Htail]; split; [|now apply Hk].
  all: try (now apply He).
  destruct (V.eq_dec (R.frame_owner f) owner) as [E|E].
  - destruct (@dormant_saved tf after owner Hpure) as [result Hsaved]; exists result;
      rewrite E; split; [exact Hsaved|right; right; exact Hbound].
  - destruct Hframe as [result [Hsaved Hi]]; exists result; split.
    + eapply (@saved_transport tf before after (Some owner)); [exact Ht|congruence|exact Hsaved].
    + eapply (@transport_incoming before after (Some owner)); [exact Ht|congruence|exact Hi].
Qed.
Lemma queue_remove_ranked st target xs : ranked_list st xs -> ranked_list st (R.queue_remove target xs).
Proof.
  intros H; apply Forall_forall; intros x Hin; exact (proj1 (Forall_forall _ _) H x (@queue_remove_members target xs x Hin)).
Qed.
Lemma queue_remove_sorted st target xs : sorted_queue st xs -> sorted_queue st (R.queue_remove target xs).
Proof.
  intro H; induction H as [|x xs Hxs IH Hbelow]; cbn; [constructor|].
  destruct (V.eq_dec target x); [exact Hxs|]; constructor; [exact IH|].
  apply Forall_forall; intros y Hy; exact (proj1 (Forall_forall _ _) Hbelow y (@queue_remove_members target xs y Hy)).
Qed.
Definition dirty_finish st target (value : option D.t) :=
  let base := R.cancel_dirty_target (R.promote_controlled st target) target in
  match value with None => base | Some v => R.write_dirty_value base target v end.
Lemma dirty_finish_metadata st target value :
  R.ranking (dirty_finish st target value) = R.ranking st /\
  R.dormant_bottom (dirty_finish st target value) = R.dormant_bottom st /\
  R.contributions (dirty_finish st target value) = R.contributions st /\
  R.requested_spawns (dirty_finish st target value) = R.requested_spawns st /\
  R.pending_spawns (dirty_finish st target value) = R.pending_spawns st /\
  R.queue (dirty_finish st target value) = R.queue_remove target (R.queue st).
Proof. destruct value; repeat split; reflexivity. Qed.
Lemma dirty_finish_value st target value :
  R.sigma_value (dirty_finish st target value) target =
  match value with None => R.sigma_value st target | Some v => v end.
Proof. destruct value; [unfold R.sigma_value,dirty_finish; cbn; now rewrite ML.lookup_update_same|reflexivity]. Qed.
Lemma dirty_finish_lookup_other st target value x : x <> target ->
  R.semantic_lookup (dirty_finish st target value) x = R.semantic_lookup st x.
Proof.
  intro H; destruct value; [unfold dirty_finish,R.semantic_lookup; cbn; now rewrite ML.lookup_update_other by congruence|reflexivity].
Qed.
Lemma dirty_finish_sigma_other st target value x : x <> target ->
  R.sigma_value (dirty_finish st target value) x = R.sigma_value st x.
Proof.
  intro H; destruct value; [unfold dirty_finish,R.sigma_value; cbn; now rewrite ML.lookup_update_other by congruence|reflexivity].
Qed.
Lemma dirty_finish_solved st target value x : solved st target ->
  (solved (dirty_finish st target value) x <-> solved st x).
Proof.
  intro Htarget; destruct (V.eq_dec x target) as [->|Hneq].
  - split; [intros; exact Htarget|intros _]; destruct value;
      [apply solved_cases; left; unfold dirty_finish; cbn; eexists; apply ML.lookup_update_same|exact Htarget].
  - unfold solved,Sem.solved; rewrite dirty_finish_lookup_other by assumption; reflexivity.
Qed.
Lemma dirty_finish_pending st target value x : x <> target -> pending st x -> pending (dirty_finish st target value) x.
Proof.
  intros Hneq [Hq|Hw]; unfold pending,dirty_finish,R.cancel_dirty_target; destruct value; cbn.
  - left; now apply queue_remove_other.
  - left; now apply queue_remove_other.
  - right; apply queue_many_members; now right.
  - now right.
Qed.
Lemma dirty_finish_reader_subset st target value key owner :
  S.mem owner (R.lookup_set (R.readers (dirty_finish st target value)) key) = true ->
  S.mem owner (R.lookup_set (R.readers st) key) = true.
Proof.
  destruct value; [|exact (fun H => H)]; unfold dirty_finish,R.lookup_set; cbn.
  destruct (V.eq_dec key target) as [->|Hneq].
  - rewrite ML.lookup_update_same,SL.empty_spec; discriminate.
  - now rewrite ML.lookup_update_other by congruence.
Qed.
Lemma dirty_finish_read_guard st target value owner key observed : owner <> target ->
  read_guard st owner key observed -> read_guard (dirty_finish st target value) owner key observed.
Proof.
  intros Howner [Hp|[Hl Hr]]; [left; now apply dirty_finish_pending|].
  destruct value as [v|]; [|right; now split].
  destruct (V.eq_dec key target) as [->|Hkey].
  - left; right; unfold dirty_finish; cbn; apply queue_many_members; left; now apply SL.mem_spec.
  - right; split; [now rewrite dirty_finish_lookup_other|].
    unfold dirty_finish,R.lookup_set; cbn; now rewrite ML.lookup_update_other by congruence.
Qed.
Lemma dirty_finish_queue_shape st target value :
  ranked_list st (R.queue st) -> sorted_queue st (R.queue st) ->
  ranked_list st (R.deferred_wakes st) -> sorted_queue st (R.deferred_wakes st) ->
  (forall reader, S.mem reader (R.lookup_set (R.readers st) target) = true -> ranked st reader) ->
  RankLaws.valid (R.ranking st) ->
  ranked_list (dirty_finish st target value) (R.queue (dirty_finish st target value)) /\
  sorted_queue (dirty_finish st target value) (R.queue (dirty_finish st target value)) /\
  ranked_list (dirty_finish st target value) (R.deferred_wakes (dirty_finish st target value)) /\
  sorted_queue (dirty_finish st target value) (R.deferred_wakes (dirty_finish st target value)).
Proof.
  intros Hq Hqo Hw Hwo Hr Hv.
  assert (Hreaders : ranked_list st (S.elements (R.lookup_set (R.readers st) target))).
  { apply Forall_forall; intros x H; apply Hr; now apply SL.mem_spec. }
  destruct value; cbn [dirty_finish]; repeat split.
  all: try first [exact (queue_remove_ranked target Hq)|exact (queue_remove_sorted target Hqo)|exact Hw|exact Hwo].
  - exact (queue_many_ranked Hreaders Hw).
  - exact (queue_many_sorted Hreaders Hw Hv Hwo).
Qed.

Lemma dirty_finish_materialized_other st target value x : x <> target ->
  R.is_materialized (dirty_finish st target value) x = R.is_materialized st x.
Proof.
  intro H; destruct value; [unfold dirty_finish,R.is_materialized; cbn; now rewrite ML.lookup_update_other by congruence|reflexivity].
Qed.
Lemma dirty_finish_preserves tf roots st ctrl target direct value :
  R.is_materialized st target = true -> tf target = Syntax.Ret direct ->
  R.pure_bottom_rhs tf target = true ->
  D.leq (R.aggregate st target) (R.sigma_value (dirty_finish st target value) target) = true ->
  wakes_finished (configuration (dirty_finish st target value) ctrl) ->
  invariant tf roots (configuration st ctrl) ->
  invariant tf roots (configuration (dirty_finish st target value) ctrl).
Proof.
  intros Hlive Hbody Hpure Htarget_bound Hfinished Hinv;
    set (before := configuration st ctrl) in *; set (next := dirty_finish st target value);
    set (after := configuration next ctrl) in *.
  destruct (@dirty_finish_metadata st target value) as [Hrank [Hdormant [Hside [Hreq [Hfifo Hqueue]]]]].
  fold next in Hrank,Hdormant,Hside,Hreq,Hfifo,Hqueue,Htarget_bound,Hfinished.
  assert (Hvalue : forall x, x <> target -> R.sigma_value next x = R.sigma_value st x).
  { intros x H; exact (@dirty_finish_sigma_other st target value x H). }
  assert (Htarget : ranked st target) by (exact (shape_materialized (inv_shape Hinv) target Hlive)).
  assert (Hsolved_target : solved st target).
  { apply solved_cases; left; unfold R.is_materialized in Hlive; destruct (M.lookup (R.sigma st) target) eqn:E;
      [eexists; reflexivity|discriminate]. }
  assert (Hsolved_after : solved next target).
  { exact (proj2 (@dirty_finish_solved st target value target Hsolved_target) Hsolved_target). }
  assert (Hbusy : forall x, x <> target -> busy before x -> busy after x).
  { intros x Hneq [Hp|Ha]; [left; exact (@dirty_finish_pending st target value x Hneq Hp)|now right]. }
  assert (Hdem : demand_transport before after).
  { intros x [Hs|[Hb|Hseed]].
    - left; exact (proj2 (@dirty_finish_solved st target value x Hsolved_target) Hs).
    - destruct (V.eq_dec x target) as [->|Hneq]; [now left|right; left; now apply Hbusy].
    - right; right; exact Hseed. }
  assert (Hready : forall x, ready before x -> ready after x).
  { intros x [Hs|Hb].
    - left; exact (proj2 (@dirty_finish_solved st target value x Hsolved_target) Hs).
    - destruct (V.eq_dec x target) as [->|Hneq]; [now left|right; now apply Hbusy]. }
  assert (Hhistory : history_transport before after (Some target)).
  { constructor; cbn [before after configuration R.cfg_state R.cfg_control].
    - intros x key observed E H; exact (@dirty_finish_read_guard st target value x key observed ltac:(congruence) H).
    - intros x key _; change (D.leq (R.stored_contribution st x key) (R.stored_contribution next x key) = true);
      unfold R.stored_contribution; rewrite Hside; apply DL.leq_refl.
    - intros x E; change (D.leq (R.sigma_value st x) (R.sigma_value next x) = true); rewrite Hvalue by congruence; apply DL.leq_refl.
    - intros x E [Hp|[Hnot|Hb]].
      + left; exact (@dirty_finish_pending st target value x ltac:(congruence) Hp).
      + right; left; exact Hnot.
      + right; right; change (D.leq (R.aggregate next x) (R.sigma_value next x) = true); unfold R.aggregate; rewrite Hside;
          rewrite Hvalue by congruence; exact Hb.
    - apply spawn_transport; [exact Hdem|intros x H; change (S.mem x (R.requested_spawns next) = true); now rewrite Hreq].
    - exact Hready. }
  destruct Hinv as [Hshape Hsummary Hbounds Hrequests Hroots Hcontrol]; constructor.
  - destruct Hshape as [Hv Hmat Hd Hr Hqr Hwr Hqo Hwo Har Hao Hframes Hw].
    destruct (@dirty_finish_queue_shape st target value Hqr Hqo Hwr Hwo (Hr target) Hv)
      as [Hqr1 [Hqo1 [Hwr1 Hwo1]]]; constructor.
    + change (RankLaws.valid (R.ranking next)); now rewrite Hrank.
    + intros x H; unfold ranked; change (exists n, Ranks.lookup (R.ranking next) x = Some n); rewrite Hrank.
      destruct (V.eq_dec x target) as [->|Hneq]; [exact Htarget|].
      apply Hmat; change (R.is_materialized (dirty_finish st target value) x = true) in H;
        rewrite (@dirty_finish_materialized_other st target value x Hneq) in H; exact H.
    + intros x H; apply Hd; change (S.mem x (R.dormant_bottom next) = true) in H; now rewrite Hdormant in H.
    + intros key x H; unfold ranked; change (exists n, Ranks.lookup (R.ranking next) x = Some n); rewrite Hrank.
      apply Hr with key; exact (@dirty_finish_reader_subset st target value key x H).
    + exact Hqr1.
    + exact Hwr1.
    + exact Hqo1.
    + exact Hwo1.
    + unfold ranked_list,ranked; change (Forall (fun x => exists n, Ranks.lookup (R.ranking next) x = Some n) (active_owners ctrl)); now rewrite Hrank.
    + change (sorted_queue next (active_owners ctrl)); unfold sorted_queue,priority; now rewrite Hrank.
    + intros x H; exact (proj2 (@dirty_finish_solved st target value x Hsolved_target) (Hframes x H)).
    + exact Hfinished.
  - intros x H; apply (proj1 (@dirty_finish_solved st target value x Hsolved_target)) in H.
    destruct (V.eq_dec x target) as [->|Hneq]; [right; exact (@dormant_saved tf after target Hpure)|].
    destruct (Hsummary x H) as [Hb|[result Hr]]; [left; now apply Hbusy|].
    right; exists result; eapply (@saved_transport tf before after (Some target)); [exact Hhistory|congruence|exact Hr].
  - intros x; destruct (V.eq_dec x target) as [->|Hneq].
    + right; change (D.leq (R.aggregate next target) (R.sigma_value next target) = true); unfold R.aggregate; rewrite Hside; exact Htarget_bound.
    + destruct (Hbounds x) as [Hb|Hb]; [left; now apply Hbusy|right].
      change (D.leq (R.aggregate next x) (R.sigma_value next x) = true); unfold R.aggregate; rewrite Hside; rewrite Hvalue by assumption; exact Hb.
  - eapply (@requests_transport before after); [exact Hdem|exact Hreq| |exact Hrequests].
    intros x H; left; change (In x (R.pending_spawns next)); now rewrite Hfifo.
  - exact (seeds_transport Hdem Hroots).
  - eapply (@control_ret_transport tf before after target direct); [reflexivity|exact Hhistory|exact Hbody|exact Hpure| |exact Hcontrol].
    change (D.leq (R.aggregate next target) (R.sigma_value next target) = true); unfold R.aggregate; rewrite Hside; exact Htarget_bound.
Qed.

Lemma dirty_read_result tf st owner target next : R.try_dirty_read tf st owner target = Some next ->
  exists direct value,
    tf target = Syntax.Ret direct /\ R.pure_bottom_rhs tf target = true /\
    next = dirty_finish st target value /\
    D.leq (R.aggregate st target) (R.sigma_value next target) = true.
Proof.
  unfold R.try_dirty_read; destruct (V.eq_dec owner target); [discriminate|].
  destruct (R.is_side_dirty st target); [|discriminate].
  destruct (tf target) as [direct| | |] eqn:Hbody; try discriminate.
  destruct (R.equivalent direct D.bottom) eqn:Hbottom; [|discriminate].
  assert (Hpure : R.pure_bottom_rhs tf target = true) by (unfold R.pure_bottom_rhs; now rewrite Hbody).
  set (candidate := D.join direct (R.aggregate st target)); set (old := R.sigma_value st target).
  assert (Hagg : D.leq (R.aggregate st target) candidate = true) by (apply DL.join_upper_right).
  destruct (R.equivalent candidate old) eqn:Hsame.
  - intro H; inversion H; subst next; exists direct,None; split; [reflexivity|]; split; [exact Hpure|]; split; [reflexivity|].
    change (D.leq (R.aggregate st target) (R.sigma_value (dirty_finish st target None) target) = true).
    rewrite dirty_finish_value; apply equivalent_true in Hsame as [Hcovered _]; eapply DL.leq_trans; eassumption.
  - destruct (S.mem target (R.controlled st)) eqn:Hcontrolled.
    + destruct (U.update false target (U.initial_phase false target) old candidate) as [phase updated] eqn:Hupdate; cbn.
      pose proof (OSL.update_sound target (U.initial_phase false target) old candidate) as Hcovered;
        rewrite Hupdate in Hcovered; cbn in Hcovered.
      destruct (D.leq old updated); [|discriminate].
      destruct (R.equivalent updated old) eqn:Hstutter.
      * intro H; inversion H; subst next; exists direct,None; split; [reflexivity|]; split; [exact Hpure|]; split; [reflexivity|].
        change (D.leq (R.aggregate st target) (R.sigma_value (dirty_finish st target None) target) = true).
        rewrite dirty_finish_value; apply equivalent_true in Hstutter as [Hlast _].
        eapply DL.leq_trans; [exact Hagg|eapply DL.leq_trans; eassumption].
      * intro H; inversion H; subst next; exists direct,(Some updated); split; [reflexivity|]; split; [exact Hpure|]; split; [reflexivity|].
        change (D.leq (R.aggregate st target) (R.sigma_value (dirty_finish st target (Some updated)) target) = true).
        rewrite dirty_finish_value; eapply DL.leq_trans; eassumption.
    + destruct (D.leq old candidate); [|discriminate].
      intro H; inversion H; subst next; exists direct,(Some candidate); split; [reflexivity|]; split; [exact Hpure|]; split; [reflexivity|].
      change (D.leq (R.aggregate st target) (R.sigma_value (dirty_finish st target (Some candidate)) target) = true).
      now rewrite dirty_finish_value.
Qed.
Lemma dirty_read_preserves tf roots st fr target tail k next :
  R.is_materialized st target = true -> R.try_dirty_read tf st (R.frame_owner fr) target = Some next ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  invariant tf roots (configuration next (R.RunRhs fr (Syntax.Get target tail) k)).
Proof.
  intros Hlive Hread Hinv; destruct (@dirty_read_result tf st (R.frame_owner fr) target next Hread) as [direct [value [Hbody [Hpure [-> Hbound]]]]].
  exact (@dirty_finish_preserves tf roots st (R.RunRhs fr (Syntax.Get target tail) k) target direct value
    Hlive Hbody Hpure Hbound I Hinv).
Qed.

Lemma finish_get_preserves tf roots st fr next_fr target tail k value :
  R.frame_owner next_fr = R.frame_owner fr ->
  R.frame_local_side next_fr = R.frame_local_side fr ->
  R.frame_current_targets next_fr = R.frame_current_targets fr ->
  R.semantic_lookup st target = Some value ->
  S.mem (R.frame_owner fr) (R.lookup_set (R.readers st) target) = true ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  invariant tf roots (configuration st (R.RunRhs next_fr (tail value) k)).
Proof.
  intros Howner Hlocal Htargets Hl Hr Hinv.
  set (before := configuration st (R.RunRhs fr (Syntax.Get target tail) k)) in *;
    set (after := configuration st (R.RunRhs next_fr (tail value) k)).
  assert (Hv : logical_view before after).
  { apply control_view; cbn [active_owners framed_owners seed_owners]; rewrite ?Howner; reflexivity. }
  eapply (@invariant_view tf roots before after Hv); [intros; exact I| |exact Hinv].
  destruct (inv_control Hinv) as [He Hk]; split.
  - eapply (@evaluation_frame tf after fr next_fr); [symmetry; exact Howner|symmetry; exact Hlocal|symmetry; exact Htargets|].
    eapply evaluation_get; [exact (@evaluation_view tf before after fr _ Hv He)|right; now split].
  - exact (@continuation_view tf before after k Hv Hk).
Qed.
Lemma materialize_is_materialized st target : R.is_materialized (R.materialize st target) target = true.
Proof.
  unfold R.materialize,R.is_materialized; destruct (M.lookup (R.sigma st) target) eqn:E;
    [now rewrite E|cbn; now rewrite ML.lookup_update_same].
Qed.
Lemma materialized_solved st target : R.is_materialized st target = true -> solved st target.
Proof.
  unfold R.is_materialized; destruct (M.lookup (R.sigma st) target) eqn:E; [|discriminate].
  intros _; apply solved_cases; left; eexists; exact E.
Qed.
Lemma dirty_result_rank tf st owner target next : R.try_dirty_read tf st owner target = Some next ->
  R.ranking next = R.ranking st.
Proof.
  intro H; destruct (@dirty_read_result tf st owner target next H) as [direct [value [_ [_ [-> _]]]]].
  exact (proj1 (@dirty_finish_metadata st target value)).
Qed.
Lemma dirty_result_materialized tf st owner target next :
  R.is_materialized st target = true -> R.try_dirty_read tf st owner target = Some next ->
  R.is_materialized next target = true.
Proof.
  intros Hlive H; destruct (@dirty_read_result tf st owner target next H) as [direct [value [_ [_ [-> _]]]]].
  destruct value; [unfold R.is_materialized,dirty_finish; cbn; now rewrite ML.lookup_update_same|exact Hlive].
Qed.
Lemma dirty_get_preserves tf roots st fr target tail k next next_fr value :
  R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  R.is_materialized st target = true -> ranked st target ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  invariant tf roots (configuration next (R.RunRhs next_fr (tail value) k)).
Proof.
  intros Hresult Hlive Htarget Hinv.
  set (ctrl := R.RunRhs fr (Syntax.Get target tail) k) in *.
  set (st1 := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  assert (Hst1_rank : R.ranking st1 = R.ranking st) by (unfold st1; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity).
  assert (Hst1_live : R.is_materialized st1 target = true) by
    (unfold st1; destruct (R.rank_lt st (R.frame_owner fr) target); exact Hlive).
  assert (Hst1_inv : invariant tf roots (configuration st1 ctrl)).
  { unfold st1; destruct (R.rank_lt st (R.frame_owner fr) target); [exact Hinv|now apply controlled_preserves]. }
  set (prepared := R.materialize st1 target).
  assert (Hprepared_live : R.is_materialized prepared target = true) by apply materialize_is_materialized.
  assert (Hprepared_rank : R.ranking prepared = R.ranking st).
  { unfold prepared,R.materialize; destruct (M.lookup (R.sigma st1) target); exact Hst1_rank. }
  assert (Hprepared_inv : invariant tf roots (configuration prepared ctrl)).
  { apply materialize_state_preserves; [unfold ranked; rewrite Hst1_rank; exact Htarget| |exact Hst1_inv].
    left; now apply materialized_solved. }
  set (flushed := match R.try_dirty_read tf prepared (R.frame_owner fr) target with Some s => s | None => prepared end).
  assert (Hflushed_inv : invariant tf roots (configuration flushed ctrl)).
  { unfold flushed; destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:E;
      [exact (@dirty_read_preserves tf roots prepared fr target tail k s Hprepared_live E Hprepared_inv)|exact Hprepared_inv]. }
  assert (Hflushed_live : R.is_materialized flushed target = true).
  { unfold flushed; destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:E;
      [exact (@dirty_result_materialized tf prepared (R.frame_owner fr) target s Hprepared_live E)|exact Hprepared_live]. }
  assert (Howner : ranked flushed (R.frame_owner fr)).
  { pose proof (shape_stack_ranks (inv_shape Hflushed_inv)) as H;
    change (ranked_list flushed (R.frame_owner fr :: suspended_owners k)) in H; now inversion H. }
  pose proof (@reader_state_preserves tf roots flushed ctrl target (R.frame_owner fr) Howner Hflushed_inv) as Hregistered.
  unfold R.dirty_complete_get in Hresult; fold st1 prepared flushed in Hresult;
    inversion Hresult; subst next next_fr value.
  eapply (@finish_get_preserves tf roots _ fr _ target tail k _); try reflexivity; [| |exact Hregistered].
  - apply solved_value; apply materialized_solved; exact Hflushed_live.
  - apply reader_mem_add; now left.
Qed.

(** Discovery knowledge is separate from the semantic history: only recorded
    targets and suspended reads need it. It introduces no additional solver. *)
Definition frame_known st fr :=
  (forall x, S.mem x (R.frame_current_targets fr) = true -> ranked st x) /\
  (forall x, S.mem x (R.frame_previous_targets fr) = true -> ranked st x).
Definition targets_known st := forall source target,
  S.mem target (R.lookup_set (R.last_targets st) source) = true -> ranked st target.
Fixpoint continuation_known st k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => True
  | R.KAfterGet fr target _ rest => frame_known st fr /\ ranked st target /\ continuation_known st rest
  | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest | R.KDrain fr rest => frame_known st fr /\ continuation_known st rest
  | R.KDead fr _ pending rest => frame_known st fr /\ ranked_list st pending /\ continuation_known st rest
  end.
Definition control_known st ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
  | R.StartEpisode _ k | R.Return k => continuation_known st k
  | R.RunRhs fr _ k | R.RunCommit fr _ k | R.RunDrain fr k => frame_known st fr /\ continuation_known st k
  | R.RunDead fr _ pending k => frame_known st fr /\ ranked_list st pending /\ continuation_known st k
  end.
Definition discovery_known c := targets_known (R.cfg_state c) /\ control_known (R.cfg_state c) (R.cfg_control c).
Definition discovery_transport st next := rank_extension st next /\ R.last_targets next = R.last_targets st.
Lemma discovery_refl st : discovery_transport st st.
Proof. split; [apply rank_extension_refl|reflexivity]. Qed.
Lemma discovery_same st next : R.ranking next = R.ranking st -> R.last_targets next = R.last_targets st ->
  discovery_transport st next.
Proof. intros Hr Ht; split; [intros x n H; now rewrite Hr|exact Ht]. Qed.
Lemma frame_known_transport st next fr : rank_extension st next -> frame_known st fr -> frame_known next fr.
Proof. intros Hr [Hc Hp]; split; intros x H; apply (@ranked_extension st next x Hr); auto. Qed.
Lemma continuation_known_transport st next k : rank_extension st next ->
  continuation_known st k -> continuation_known next k.
Proof.
  intro Hr; induction k; cbn; try exact (fun H => H).
  - intros [Hf [Ht Hk]]; split; [now apply frame_known_transport with st|]; split;
      [now apply ranked_extension with st|now apply IHk].
  - intros [Hf Hk]; split; [now apply frame_known_transport with st|now apply IHk].
  - intros [Hf Hk]; split; [now apply frame_known_transport with st|now apply IHk].
  - intros [Hf [Hp Hk]]; split; [now apply frame_known_transport with st|]; split;
      [now apply ranked_list_extension with st|now apply IHk].
  - intros [Hf Hk]; split; [now apply frame_known_transport with st|now apply IHk].
Qed.
Lemma control_known_transport st next ctrl : rank_extension st next -> control_known st ctrl -> control_known next ctrl.
Proof.
  intro Hr; destruct ctrl; cbn; try exact (fun H => H);
    try (now apply continuation_known_transport).
  all: intros [Hf Hrest]; split; [now apply frame_known_transport with st|].
  all: try (now apply continuation_known_transport with st).
  destruct Hrest as [Hp Hk]; split; [now apply ranked_list_extension with st|now apply continuation_known_transport with st].
Qed.
Lemma targets_known_transport st next : discovery_transport st next -> targets_known st -> targets_known next.
Proof.
  intros [Hr Htable] Hknown source target H; rewrite Htable in H.
  eapply ranked_extension; [exact Hr|exact (Hknown source target H)].
Qed.
Lemma discovery_known_transport st next ctrl : discovery_transport st next ->
  discovery_known (configuration st ctrl) -> discovery_known (configuration next ctrl).
Proof.
  intros [Hr Htable] [Ht Hc]; split;
    [exact (@targets_known_transport st next (conj Hr Htable) Ht)|exact (@control_known_transport st next ctrl Hr Hc)].
Qed.
Lemma frame_known_fields st fr next_fr :
  R.frame_current_targets next_fr = R.frame_current_targets fr ->
  R.frame_previous_targets next_fr = R.frame_previous_targets fr ->
  frame_known st fr -> frame_known st next_fr.
Proof. intros Hc Hp; unfold frame_known; now rewrite Hc,Hp. Qed.
Lemma frame_known_read st fr minimum maximum : frame_known st fr -> frame_known st (R.with_frame_read fr minimum maximum).
Proof. apply frame_known_fields; reflexivity. Qed.
Lemma frame_known_phase st fr phase : frame_known st fr -> frame_known st (R.with_frame_phase fr phase).
Proof. apply frame_known_fields; reflexivity. Qed.
Lemma frame_known_side st fr target value : ranked st target -> frame_known st fr ->
  frame_known st (R.with_frame_side fr target value).
Proof.
  intros Htarget [Hc Hp]; split; [|exact Hp]; intros x H; cbn in H; apply SL.add_spec in H as [->|H];
    [exact Htarget|now apply Hc].
Qed.
Lemma frame_known_fresh st owner phase : targets_known st -> frame_known st (R.fresh_frame st owner phase).
Proof.
  intro H; split; intros x Hx; cbn in Hx;
    [rewrite SL.empty_spec in Hx; discriminate|exact (H owner x Hx)].
Qed.
Lemma publish_targets_known st fr : targets_known st -> frame_known st fr -> targets_known (R.publish_targets st fr).
Proof.
  intros Ht [Hc Hp] source target H; change (ranked st target).
  unfold R.publish_targets,R.lookup_set in H; cbn in H;
    destruct (V.eq_dec source (R.frame_owner fr)) as [->|Hneq].
  - rewrite ML.lookup_update_same in H; exact (Hc target H).
  - rewrite ML.lookup_update_other in H by congruence; exact (Ht source target H).
Qed.
Lemma initial_discovery_known roots : discovery_known (R.initial_config roots).
Proof.
  split; [|exact I]; intros source target H; change (S.mem target (R.lookup_set (M.empty S.t) source) = true) in H;
    unfold R.lookup_set in H; rewrite ML.lookup_empty,SL.empty_spec in H; discriminate.
Qed.
Lemma discovery_observe st target : discovery_transport st (R.observe st target).
Proof. split; [apply observe_extends|unfold R.observe; destruct (Ranks.observe (R.ranking st) target); reflexivity]. Qed.
Lemma discovery_materialize st target : discovery_transport st (R.materialize st target).
Proof. unfold R.materialize; destruct (M.lookup (R.sigma st) target); apply discovery_same; reflexivity. Qed.
Lemma discovery_reset st owner : discovery_transport st (R.reset_registered_cells st owner).
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; apply discovery_same; reflexivity. Qed.
Lemma discovery_request st target : discovery_transport st (R.request_spawn st target).
Proof. unfold R.request_spawn; destruct (S.mem target (R.requested_spawns st)); apply discovery_same; reflexivity. Qed.
Lemma discovery_complete_get st fr target next next_fr value :
  R.complete_get st fr target = (next,next_fr,value) -> discovery_transport st next /\
  R.frame_current_targets next_fr = R.frame_current_targets fr /\
  R.frame_previous_targets next_fr = R.frame_previous_targets fr.
Proof.
  unfold R.complete_get; intro H; inversion H; subst; split; [|now split].
  unfold R.materialize; destruct (M.lookup _ _); apply discovery_same;
    destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
Qed.
Lemma discovery_side_write st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) -> discovery_transport st next.
Proof.
  unfold R.write_side_contribution; intro H; inversion H; subst; apply discovery_same;
    unfold R.register_reset; cbn; unfold R.promote_side_target;
    destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
Qed.
Lemma discovery_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  discovery_transport st next /\ R.frame_current_targets next_fr = R.frame_current_targets fr /\
  R.frame_previous_targets next_fr = R.frame_previous_targets fr.
Proof.
  intro H; apply set_value_cases in H as [[_ [-> ->]]|[_ [Hframe [[_ ->]|[_ ->]]]]].
  - split; [apply discovery_refl|now split].
  - split; [apply discovery_refl|]; rewrite Hframe; now split.
  - split; [apply discovery_same; reflexivity|]; rewrite Hframe; now split.
Qed.
Lemma discovery_dirty_read tf st owner target next : R.try_dirty_read tf st owner target = Some next -> discovery_transport st next.
Proof.
  intro H; destruct (@dirty_read_result tf st owner target next H) as [direct [value [_ [_ [-> _]]]]].
  destruct value; apply discovery_same; reflexivity.
Qed.
Lemma discovery_dirty_get tf st fr target next next_fr value :
  R.dirty_complete_get tf st fr target = (next,next_fr,value) -> discovery_transport st next /\
  R.frame_current_targets next_fr = R.frame_current_targets fr /\
  R.frame_previous_targets next_fr = R.frame_previous_targets fr.
Proof.
  unfold R.dirty_complete_get.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  set (prepared := R.materialize base target).
  assert (Hprepared : discovery_transport st prepared).
  { unfold prepared; destruct (discovery_materialize base target) as [Hr Ht]; split.
    - eapply rank_extension_trans; [|exact Hr]; unfold base; destruct (R.rank_lt st (R.frame_owner fr) target); change (rank_extension st st); apply rank_extension_refl.
    - rewrite Ht; unfold base; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity. }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:E; intro H; inversion H; subst; split; [|now split| |now split].
  - destruct (@discovery_dirty_read tf prepared (R.frame_owner fr) target s E) as [Hr Ht];
      destruct Hprepared as [Hr0 Ht0]; split; [eapply rank_extension_trans; eassumption|cbn; now rewrite Ht,Ht0].
  - destruct Hprepared; split; [assumption|assumption].
Qed.

Definition get_cursor (dirty : bool) tf st fr target tail k :=
  let '(next,next_fr,value) :=
    if dirty then R.dirty_complete_get tf st fr target else R.complete_get st fr target in
  configuration next (R.RunRhs next_fr (tail value) k).
Definition observed_get (dirty : bool) tf st fr target tail k :=
  if R.is_materialized st target then get_cursor dirty tf st fr target tail k
  else if R.rank_lt st (R.frame_owner fr) target
  then configuration st (R.StartEpisode target (R.KAfterGet fr target tail k))
  else get_cursor false tf (R.enqueue st target) fr target tail k.
Lemma get_cursor_preserves tf roots dirty st fr target tail k :
  ranked st target -> R.is_materialized st target = true ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  invariant tf roots (get_cursor dirty tf st fr target tail k).
Proof.
  intros Htarget Hlive Hinv; unfold get_cursor; destruct dirty.
  - destruct (R.dirty_complete_get tf st fr target) as [[next next_fr] value] eqn:E;
      exact (@dirty_get_preserves tf roots st fr target tail k next next_fr value E Hlive Htarget Hinv).
  - destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:E;
      apply (@get_resume_preserves tf roots st fr target tail k next next_fr value E Htarget);
      [left; now apply materialized_solved|exact Hinv].
Qed.
Lemma observed_get_preserves tf roots dirty st fr target tail k : ranked st target ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  invariant tf roots (observed_get dirty tf st fr target tail k).
Proof.
  intros Htarget Hinv; unfold observed_get; destruct (R.is_materialized st target) eqn:Hlive.
  - exact (@get_cursor_preserves tf roots dirty st fr target tail k Htarget Hlive Hinv).
  - destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hlt.
    + exact (@get_child_preserves tf roots st fr target tail k Htarget Hlt Hinv).
    + unfold get_cursor; destruct (R.complete_get (R.enqueue st target) fr target) as [[next next_fr] value] eqn:E.
      exact (@get_queued_preserves tf roots st fr target tail k next next_fr value Htarget E Hinv).
Qed.
Definition observed_spawn st fr target tail k :=
  if R.is_materialized st target then configuration st (R.RunRhs fr tail k)
  else if R.rank_lt st (R.frame_owner fr) target
  then configuration st (R.StartEpisode target (R.KAfterSpawn fr tail k))
  else configuration (R.materialize (R.enqueue st target) target) (R.RunRhs fr tail k).
Lemma observed_spawn_preserves tf roots st fr target tail k : ranked st target ->
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  invariant tf roots (observed_spawn st fr target tail k).
Proof.
  intros Htarget Hinv; unfold observed_spawn; destruct (R.is_materialized st target) eqn:Hlive.
  - apply (@spawn_solved_preserves tf roots st fr target tail k); [now apply materialized_solved|exact Hinv].
  - destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hlt;
      [exact (@spawn_child_preserves tf roots st fr target tail k Htarget Hlt Hinv)|
       exact (@spawn_queued_preserves tf roots st fr target tail k Htarget Hinv)].
Qed.
Lemma option_cursor (getter : (R.state * R.frame) * D.t) tail k :
  (let '(next,next_fr,value) := getter in Some (configuration next (R.RunRhs next_fr (tail value) k))) =
  Some (let '(next,next_fr,value) := getter in configuration next (R.RunRhs next_fr (tail value) k)).
Proof. destruct getter as [[next next_fr] value]; reflexivity. Qed.
Lemma rhs_step_preserves tf roots st fr body k after :
  R.next_config tf (configuration st (R.RunRhs fr body k)) = Some after ->
  invariant tf roots (configuration st (R.RunRhs fr body k)) -> invariant tf roots after.
Proof.
  destruct body as [direct|target tail|target raw tail|target tail];
    unfold R.next_config,configuration; cbn [R.cfg_state R.cfg_control].
  - intros E H; inversion E; subst; now apply ret_preserves.
  - intros E Hinv; destruct (R.is_dormant st target) eqn:Hdormant.
    + inversion E; subst; apply dormant_get_preserves; [now apply is_dormant_lookup|exact Hinv].
    + pose proof (@observe_preserves tf roots st (R.RunRhs fr (Syntax.Get target tail) k) target Hinv) as Hobserved;
        pose proof (@observe_ranks st target) as Htarget.
      destruct (Ranks.lookup (R.ranking st) target) eqn:Hrank.
      * rewrite ?option_cursor in E.
        assert (Eget : Some (observed_get true tf (R.observe st target) fr target tail k) = Some after).
        { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target);
            [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
        inversion Eget; subst; now apply observed_get_preserves.
      * destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)) eqn:Hpure.
        -- apply andb_true_iff in Hpure as [Hpure Hlive]; apply negb_true_iff in Hlive.
           inversion E; subst; apply dormant_get_preserves;
             [apply remembered_lookup; now apply unmaterialized_lookup|now apply remember_dormant_preserves].
        -- assert (Eget : Some (observed_get false tf (R.observe st target) fr target tail k) = Some after).
           { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target) eqn:Hlive; cbn in E; rewrite ?option_cursor in E;
               [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
           inversion Eget; subst; now apply observed_get_preserves.
  - intros E Hinv; pose proof (@observe_preserves tf roots st
      (R.RunRhs fr (Syntax.Side target raw tail) k) target Hinv) as Hobserved.
    pose proof (@observe_ranks st target) as Htarget.
    cbn [R.record_side_input] in E.
    destruct (R.write_side_contribution (R.observe st target)
      (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) target
      (R.accumulated_side_input fr target raw)) as [next changed] eqn:Hwrite.
    destruct (R.is_dormant st target) eqn:Hwas.
    + inversion E; subst; exact (@side_progress_preserves tf roots (R.observe st target) fr target raw tail k
        next changed true Hwrite ltac:(discriminate) Htarget Hobserved).
    + destruct changed.
      * inversion E; subst; apply (@dirty_side_preserves tf roots next
          (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) target tail k true).
        exact (@side_progress_preserves tf roots (R.observe st target) fr target raw tail k
          next true true Hwrite ltac:(discriminate) Htarget Hobserved).
      * inversion E; subst; exact (@side_progress_preserves tf roots (R.observe st target) fr target raw tail k
          next false false Hwrite ltac:(intros; reflexivity) Htarget Hobserved).
  - intros E Hinv; destruct Features.defer_spawns.
    + inversion E; subst; now apply deferred_spawn_preserves.
    + destruct (R.is_dormant st target) eqn:Hdormant.
      * inversion E; subst; apply (@spawn_solved_preserves tf roots st fr target tail k);
          [exists D.bottom; now apply is_dormant_lookup|exact Hinv].
      * pose proof (@observe_preserves tf roots st (R.RunRhs fr (Syntax.Spawn target tail) k) target Hinv) as Hobserved;
          pose proof (@observe_ranks st target) as Htarget.
        destruct (Ranks.lookup (R.ranking st) target) eqn:Hrank.
        -- assert (Espawn : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
           { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
               [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
           inversion Espawn; subst; now apply observed_spawn_preserves.
        -- destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)) eqn:Hpure.
           ++ apply andb_true_iff in Hpure as [Hpure _]; inversion E; subst; apply (@spawn_solved_preserves tf roots (R.remember_dormant st target) fr target tail k);
                [apply dormant_solves|now apply remember_dormant_preserves].
           ++ assert (Espawn : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
              { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
                  [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
              inversion Espawn; subst; now apply observed_spawn_preserves.
Qed.

Lemma solved_flag st target : R.is_materialized st target || R.is_dormant st target = true -> solved st target.
Proof.
  rewrite orb_true_iff; intros [H|H]; [now apply materialized_solved|exists D.bottom; now apply is_dormant_lookup].
Qed.
Lemma invariant_step tf roots before after : R.next_config tf before = Some after ->
  discovery_known before -> invariant tf roots before -> invariant tf roots after.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hstep Hknown Hinv.
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
      destruct (R.queue st) as [|owner tail] eqn:Hqueue; cbn [R.queue_pop] in Hstep.
    + destruct (R.pending_spawns st) as [|target tail] eqn:Hfifo; [discriminate|].
      inversion Hstep; subst; exact (@fifo_start_preserves tf roots st target tail Hfifo Hinv).
    + inversion Hstep; subst; exact (@loop_pop_preserves tf roots st owner tail Hqueue Hinv).
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep; destruct seeds as [|owner tail].
    + inversion Hstep; subst; exact (@empty_seeds_preserves tf roots st Hinv).
    + destruct (R.is_materialized st owner || R.is_dormant st owner) eqn:Hsolved.
      * inversion Hstep; subst; apply (@skip_seed_preserves tf roots st owner tail);
          [now apply solved_flag|exact Hinv].
      * pose proof (@observe_preserves tf roots st (R.RunSeeds (owner :: tail)) owner Hinv) as Hobs;
          pose proof (@observe_ranks st owner) as Hr.
        destruct (Ranks.lookup (R.ranking st) owner) eqn:Hrank.
        -- inversion Hstep; subst; exact (@start_seed_preserves tf roots (R.observe st owner) owner tail Hr Hobs).
        -- destruct (R.pure_bottom_rhs tf owner) eqn:Hpure.
           ++ inversion Hstep; subst; apply (@skip_seed_preserves tf roots (R.remember_dormant st owner) owner tail);
                [apply dormant_solves|exact (@remember_dormant_preserves tf roots st (R.RunSeeds (owner::tail)) owner Hpure Hinv)].
           ++ inversion Hstep; subst; exact (@start_seed_preserves tf roots (R.observe st owner) owner tail Hr Hobs).
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
      destruct (R.queue st) as [|owner tail] eqn:Hqueue; cbn [R.queue_pop] in Hstep; inversion Hstep; subst.
    + exact (@seed_loop_idle_preserves tf roots st remaining Hinv).
    + exact (@seed_loop_pop_preserves tf roots st remaining owner tail Hqueue Hinv).
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
      inversion Hstep; subst; exact (@start_episode_preserves tf roots st owner k Hinv).
  - exact (@rhs_step_preserves tf roots st fr body k after Hstep Hinv).
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep; destruct pending as [|target tail].
    + inversion Hstep; subst; exact (@finish_dead_preserves tf roots st fr direct k Hinv).
    + destruct Hknown as [Ht [Hfr [Hp Hk]]];
        change (ranked_list st (target :: tail)) in Hp; inversion Hp as [|? ? Hr Hrest]; subst.
      destruct (S.mem target (R.frame_current_targets fr)) eqn:Hcurrent.
      * inversion Hstep; subst; exact (@dead_skip_preserves tf roots st fr direct (target::tail) k Hinv tail).
      * destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite;
          inversion Hstep; subst.
        exact (@dead_progress_preserves tf roots st fr direct target tail k next changed Hwrite Hcurrent Hr Hinv).
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
      destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:Hwrite;
      inversion Hstep; subst; exact (@commit_preserves tf roots st fr direct k next next_fr Hwrite Hinv).
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
      destruct (R.queue st) as [|head tail] eqn:Hqueue; cbn [R.queue_peek R.queue_pop] in Hstep.
    + inversion Hstep; subst; exact (@drain_empty_preserves tf roots st fr k Hqueue Hinv).
    + destruct (V.eq_dec head (R.frame_owner fr)) as [E|Hneq].
      * subst head; inversion Hstep; subst; exact (@restart_preserves tf roots st fr k tail Hqueue Hinv).
      * destruct (R.rank_lt st (R.frame_owner fr) head) eqn:Hlt; inversion Hstep; subst.
        -- exact (@drain_child_preserves tf roots st fr k head tail Hqueue Hlt Hinv).
        -- exact (@drain_lower_preserves tf roots st fr k head tail Hqueue Hneq Hlt Hinv).
  - destruct k as [|seeds|fr target tail k|fr tail k|fr tail k|fr direct pending k|fr k];
      unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
    + inversion Hstep; subst; exact (@return_loop_preserves tf roots st Hinv).
    + inversion Hstep; subst; exact (@return_seeds_preserves tf roots st seeds Hinv).
    + destruct Hknown as [Ht [Hfr [Hr Hk]]];
        destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:Hwrite;
        inversion Hstep; subst; exact (@return_get_preserves tf roots st fr target tail k next next_fr value Hwrite Hr Hinv).
    + inversion Hstep; subst; exact (@return_side_preserves tf roots st fr tail k Hinv).
    + inversion Hstep; subst; exact (@return_spawn_preserves tf roots st fr tail k Hinv).
    + inversion Hstep; subst; exact (@return_dead_preserves tf roots st fr direct pending k Hinv).
    + inversion Hstep; subst; exact (@return_drain_preserves tf roots st fr k Hinv).
Qed.

Lemma known_rhs_transfer st next fr next_fr body next_body k : discovery_transport st next ->
  R.frame_current_targets next_fr = R.frame_current_targets fr ->
  R.frame_previous_targets next_fr = R.frame_previous_targets fr ->
  discovery_known (configuration st (R.RunRhs fr body k)) ->
  discovery_known (configuration next (R.RunRhs next_fr next_body k)).
Proof.
  intros [Hr Ht] Hcurrent Hprevious [Htable [Hframe Hkont]]; split.
  - exact (@targets_known_transport st next (conj Hr Ht) Htable).
  - split.
    + apply (@frame_known_fields next fr next_fr Hcurrent Hprevious);
        exact (@frame_known_transport st next fr Hr Hframe).
    + exact (@continuation_known_transport st next k Hr Hkont).
Qed.
Lemma get_cursor_known dirty tf st fr target tail k :
  discovery_known (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  discovery_known (get_cursor dirty tf st fr target tail k).
Proof.
  intro H; unfold get_cursor; destruct dirty.
  - destruct (R.dirty_complete_get tf st fr target) as [[next next_fr] value] eqn:E;
      destruct (@discovery_dirty_get tf st fr target next next_fr value E) as [Ht [Hc Hp]];
      exact (@known_rhs_transfer st next fr next_fr _ _ k Ht Hc Hp H).
  - destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:E;
      destruct (@discovery_complete_get st fr target next next_fr value E) as [Ht [Hc Hp]];
      exact (@known_rhs_transfer st next fr next_fr _ _ k Ht Hc Hp H).
Qed.
Lemma observed_get_known dirty tf st fr target tail k : ranked st target ->
  discovery_known (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  discovery_known (observed_get dirty tf st fr target tail k).
Proof.
  intros Hr H; unfold observed_get; destruct (R.is_materialized st target).
  - exact (@get_cursor_known dirty tf st fr target tail k H).
  - destruct (R.rank_lt st (R.frame_owner fr) target).
    + destruct H as [Ht [Hf Hk]]; split; [exact Ht|split; [exact Hf|now split]].
    + apply get_cursor_known; apply (@discovery_known_transport st (R.enqueue st target) _);
        [apply discovery_same; reflexivity|exact H].
Qed.
Lemma observed_spawn_known st fr target tail k :
  discovery_known (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  discovery_known (observed_spawn st fr target tail k).
Proof.
  intros [Ht [Hf Hk]]; unfold observed_spawn; destruct (R.is_materialized st target);
    [split; [exact Ht|now split]|].
  destruct (R.rank_lt st (R.frame_owner fr) target); [split; [exact Ht|now split]|].
  apply (@discovery_known_transport st (R.materialize (R.enqueue st target) target) _).
  - destruct (discovery_materialize (R.enqueue st target) target) as [Hr Heq];
      split; [exact Hr|exact Heq].
  - split; [exact Ht|now split].
Qed.
Lemma continue_side_known st fr target body k changed :
  discovery_known (configuration st (R.RunRhs fr body k)) ->
  discovery_known (R.continue_side st fr target body k changed).
Proof.
  intros [Ht [Hf Hk]]; unfold R.continue_side; destruct changed.
  - destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target)).
    + exact (conj Ht (conj Hf Hk)).
    + apply (@discovery_known_transport st (R.enqueue st target) (R.RunRhs fr body k));
        [apply discovery_same; reflexivity|exact (conj Ht (conj Hf Hk))].
  - exact (conj Ht (conj Hf Hk)).
Qed.
Lemma continue_dead_known st fr direct target pending k changed :
  discovery_known (configuration st (R.RunDead fr direct pending k)) ->
  discovery_known (R.continue_dead st fr direct target pending k changed).
Proof.
  intros [Ht [Hf [Hp Hk]]]; unfold R.continue_dead; destruct changed.
  - destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target)).
    + exact (conj Ht (conj Hf (conj Hp Hk))).
    + apply (@discovery_known_transport st (R.enqueue st target) (R.RunDead fr direct pending k));
        [apply discovery_same; reflexivity|exact (conj Ht (conj Hf (conj Hp Hk)))].
  - exact (conj Ht (conj Hf (conj Hp Hk))).
Qed.
Lemma discovery_trans st middle next : discovery_transport st middle -> discovery_transport middle next -> discovery_transport st next.
Proof. intros [H1 E1] [H2 E2]; split; [eapply rank_extension_trans; eassumption|now rewrite E2,E1]. Qed.
Lemma discovery_dirty_side st fr target body k changed :
  discovery_known (R.continue_side st fr target body k changed) ->
  discovery_known (R.continue_side (R.mark_side_dirty st target) fr target body k changed).
Proof.
  unfold R.continue_side,R.mark_side_dirty,R.rank_lt,R.is_materialized; cbn;
    destruct changed; [destruct (R.ranking_lt (R.ranking st) (R.frame_owner fr) target &&
      negb (match M.lookup (R.sigma st) target with Some _ => true | None => false end))|].
  all: apply discovery_known_transport; apply discovery_same; reflexivity.
Qed.

Lemma known_plain_rhs st next fr body tail k : R.ranking next = R.ranking st ->
  R.last_targets next = R.last_targets st ->
  discovery_known (configuration st (R.RunRhs fr body k)) ->
  discovery_known (configuration next (R.RunRhs fr tail k)).
Proof.
  intros Hr Ht H; exact (@known_rhs_transfer st next fr fr body tail k
    (@discovery_same st next Hr Ht) eq_refl eq_refl H).
Qed.
Lemma rhs_discovery_step tf st fr body k after :
  R.next_config tf (configuration st (R.RunRhs fr body k)) = Some after ->
  discovery_known (configuration st (R.RunRhs fr body k)) -> discovery_known after.
Proof.
  destruct body as [direct|target tail|target raw tail|target tail];
    unfold R.next_config,configuration; cbn [R.cfg_state R.cfg_control].
  - intros E [Ht [Hfr Hk]]; inversion E; subst; split; [exact Ht|]; split; [exact Hfr|]; split; [|exact Hk].
    destruct Features.eliminate_dead_sides; [apply Forall_forall|constructor].
    intros x H; apply (proj2 Hfr); now apply SL.mem_spec.
  - intros E Hknown; destruct (R.is_dormant st target) eqn:Hdormant.
    + inversion E; subst; eapply (@known_plain_rhs st _ fr (Syntax.Get target tail)); [reflexivity|reflexivity|exact Hknown].
    + pose proof (@discovery_known_transport st (R.observe st target)
        (R.RunRhs fr (Syntax.Get target tail) k) (discovery_observe st target) Hknown) as Hobserved;
        pose proof (@observe_ranks st target) as Htarget.
      destruct (Ranks.lookup (R.ranking st) target) eqn:Hrank.
      * rewrite ?option_cursor in E.
        assert (Eget : Some (observed_get true tf (R.observe st target) fr target tail k) = Some after).
        { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target);
            [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
        inversion Eget; subst; exact (@observed_get_known true tf (R.observe st target) fr target tail k Htarget Hobserved).
      * destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)) eqn:Hpure.
        -- inversion E; subst; eapply (@known_plain_rhs st _ fr (Syntax.Get target tail)); [reflexivity|reflexivity|exact Hknown].
        -- assert (Eget : Some (observed_get false tf (R.observe st target) fr target tail k) = Some after).
           { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target) eqn:Hlive;
               cbn in E; rewrite ?option_cursor in E;
               [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
           inversion Eget; subst; exact (@observed_get_known false tf (R.observe st target) fr target tail k Htarget Hobserved).
  - intros E Hknown; pose proof (@discovery_known_transport st (R.observe st target)
      (R.RunRhs fr (Syntax.Side target raw tail) k) (discovery_observe st target) Hknown) as Hobserved.
    pose proof (@observe_ranks st target) as Htarget.
    cbn [R.record_side_input] in E.
    destruct (R.write_side_contribution (R.observe st target)
      (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) target
      (R.accumulated_side_input fr target raw)) as [next changed] eqn:Hwrite.
    assert (Hrecorded : discovery_known (configuration (R.observe st target)
      (R.RunRhs (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) tail k))).
    { destruct Hobserved as [Ht [Hfr Hk]]; split; [exact Ht|]; split;
        [exact (@frame_known_side (R.observe st target) fr target _ Htarget Hfr)|exact Hk]. }
    pose proof (@discovery_known_transport (R.observe st target) next _
      (@discovery_side_write (R.observe st target) _ target _ next changed Hwrite) Hrecorded) as Hpublished.
    destruct (R.is_dormant st target) eqn:Hwas.
    + inversion E; subst; exact (@continue_side_known next _ target tail k true Hpublished).
    + destruct changed.
      * inversion E; subst; apply (@discovery_dirty_side next (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) target tail k true);
          exact (@continue_side_known next _ target tail k true Hpublished).
      * inversion E; subst; exact (@continue_side_known next _ target tail k false Hpublished).
  - intros E Hknown; destruct Features.defer_spawns.
    + inversion E; subst; exact (@known_rhs_transfer st (R.request_spawn st target) fr fr
        (Syntax.Spawn target tail) tail k (discovery_request st target) eq_refl eq_refl Hknown).
    + destruct (R.is_dormant st target) eqn:Hdormant.
      * inversion E; subst; exact Hknown.
      * pose proof (@discovery_known_transport st (R.observe st target)
          (R.RunRhs fr (Syntax.Spawn target tail) k) (discovery_observe st target) Hknown) as Hobserved.
        destruct (Ranks.lookup (R.ranking st) target) eqn:Hrank.
        -- assert (Espawn : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
           { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
               [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
           inversion Espawn; subst; exact (@observed_spawn_known (R.observe st target) fr target tail k Hobserved).
        -- destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)) eqn:Hpure.
           ++ inversion E; subst; eapply (@known_plain_rhs st _ fr (Syntax.Spawn target tail)); [reflexivity|reflexivity|exact Hknown].
           ++ assert (Espawn : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
              { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
                  [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
              inversion Espawn; subst; exact (@observed_spawn_known (R.observe st target) fr target tail k Hobserved).
Qed.

Lemma known_fresh_cursor st next owner phase body k : discovery_transport st next ->
  targets_known st -> continuation_known st k ->
  discovery_known (configuration next (R.RunRhs (R.fresh_frame next owner phase) body k)).
Proof.
  intros [Hr Ht] Htable Hk; pose proof (@targets_known_transport st next (conj Hr Ht) Htable) as Htable1;
    split; [exact Htable1|]; split; [now apply frame_known_fresh|exact (@continuation_known_transport st next k Hr Hk)].
Qed.
Lemma discovery_step tf before after : R.next_config tf before = Some after ->
  discovery_known before -> discovery_known after.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hstep Hknown.
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
      destruct (R.queue st) as [|owner tail] eqn:Hqueue; cbn [R.queue_pop] in Hstep.
    + destruct (R.pending_spawns st) as [|target tail] eqn:Hfifo; [discriminate|]; inversion Hstep; subst; exact Hknown.
    + inversion Hstep; subst; exact Hknown.
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep; destruct seeds as [|owner tail].
    + inversion Hstep; subst; exact Hknown.
    + destruct (R.is_materialized st owner || R.is_dormant st owner).
      * inversion Hstep; subst; exact Hknown.
      * pose proof (@discovery_known_transport st (R.observe st owner) (R.RunSeeds (owner::tail))
          (discovery_observe st owner) Hknown) as Hobs.
        destruct (Ranks.lookup (R.ranking st) owner).
        -- inversion Hstep; subst; exact Hobs.
        -- destruct (R.pure_bottom_rhs tf owner); inversion Hstep; subst; [exact Hknown|exact Hobs].
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
      destruct (R.queue st) as [|owner tail] eqn:Hqueue; cbn [R.queue_pop] in Hstep; inversion Hstep; subst; exact Hknown.
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep; inversion Hstep; subst.
    destruct Hknown as [Ht Hk]; apply (@known_fresh_cursor st _ owner _ _ k); [|exact Ht|exact Hk].
    eapply discovery_trans; [apply discovery_materialize|apply discovery_same; reflexivity].
  - exact (@rhs_discovery_step tf st fr body k after Hstep Hknown).
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep; destruct pending as [|target tail].
    + inversion Hstep; subst; destruct Hknown as [Ht [Hfr [_ Hk]]]; split;
        [exact (@publish_targets_known st fr Ht Hfr)|split; [exact Hfr|
          exact (@continuation_known_transport st (R.publish_targets st fr) k (@rank_extension_refl st) Hk)]].
    + destruct Hknown as [Ht [Hfr [Hp Hk]]]; change (ranked_list st (target::tail)) in Hp;
        inversion Hp as [|? ? Hr Hrest]; subst.
      destruct (S.mem target (R.frame_current_targets fr)).
      * inversion Hstep; subst; exact (conj Ht (conj Hfr (conj Hrest Hk))).
      * destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite; inversion Hstep; subst.
        apply (@continue_dead_known _ fr direct target tail k changed).
        eapply (@discovery_known_transport st _ (R.RunDead fr direct tail k));
          [|exact (conj Ht (conj Hfr (conj Hrest Hk)))].
        eapply discovery_trans; [exact (@discovery_side_write st fr target D.bottom next changed Hwrite)|].
        destruct changed; apply discovery_same; reflexivity.
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
      destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:Hwrite; inversion Hstep; subst.
    destruct (@discovery_commit (R.flush_deferred st) fr direct next next_fr Hwrite) as [Hm [Hcurrent Hprevious]].
    assert (Htransport : discovery_transport st next).
    { eapply discovery_trans; [apply discovery_same; reflexivity|exact Hm]. }
    exact (@known_rhs_transfer st next fr next_fr (Syntax.Ret direct) (Syntax.Ret direct) k Htransport Hcurrent Hprevious Hknown).
  - unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep;
      destruct (R.queue st) as [|head tail] eqn:Hqueue; cbn [R.queue_peek R.queue_pop] in Hstep.
    + inversion Hstep; subst; destruct Hknown as [Ht [_ Hk]];
        apply (@discovery_known_transport st _ (R.Return k)); [apply discovery_reset|now split].
    + destruct (V.eq_dec head (R.frame_owner fr)) as [E|Hneq].
      * subst head; inversion Hstep; subst; destruct Hknown as [Ht [_ Hk]].
        apply (@known_fresh_cursor st _ (R.frame_owner fr) _ _ k); [apply discovery_same; reflexivity|exact Ht|exact Hk].
      * destruct (R.rank_lt st (R.frame_owner fr) head); inversion Hstep; subst.
        -- apply (@discovery_known_transport st _ (R.StartEpisode head (R.KDrain fr k)));
             [apply discovery_same; reflexivity|exact Hknown].
        -- destruct Hknown as [Ht [_ Hk]]; apply (@discovery_known_transport st _ (R.Return k));
             [apply discovery_reset|now split].
  - destruct k as [|seeds|fr target tail k|fr tail k|fr tail k|fr direct pending k|fr k];
      unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
    + inversion Hstep; subst; exact Hknown.
    + inversion Hstep; subst; exact Hknown.
    + destruct Hknown as [Ht [Hfr [_ Hk]]];
        destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:Hwrite; inversion Hstep; subst.
      destruct (@discovery_complete_get st fr target next next_fr value Hwrite) as [Hm [Hcurrent Hprevious]].
      exact (@known_rhs_transfer st next fr next_fr (Syntax.Get target tail) (tail value) k Hm Hcurrent Hprevious (conj Ht (conj Hfr Hk))).
    + inversion Hstep; subst; exact Hknown.
    + inversion Hstep; subst; exact Hknown.
    + inversion Hstep; subst; exact Hknown.
    + inversion Hstep; subst; exact Hknown.
Qed.
Lemma reachable_invariants tf roots c : Sem.steps tf (R.initial_config roots) c ->
  discovery_known c /\ invariant tf roots c.
Proof.
  intro H; remember (R.initial_config roots) as initial eqn:E in H.
  assert (Hinitial : discovery_known initial /\ invariant tf roots initial).
  { subst initial; split; [apply initial_discovery_known|apply initial_invariant]. }
  clear E; induction H; [exact Hinitial|].
  apply IHsteps; destruct Hinitial as [Hknown Hinv]; split.
  - exact (@discovery_step tf a b H Hknown).
  - exact (@invariant_step tf roots a b H Hknown Hinv).
Qed.
Theorem successful_run_correct fuel tf roots final : R.solve_fuel fuel tf roots = Some final ->
  correct_final_state tf roots final.
Proof.
  intro Hrun; destruct (@successful_path fuel tf roots final Hrun) as [Hpath Hquiet].
  apply (@invariant_terminal_correct tf roots final Hquiet).
  exact (proj2 (@reachable_invariants tf roots (Sem.terminal_config final) Hpath)).
Qed.

Lemma prefix_supported supported root body reads sides spawns :
  prefix root body reads sides spawns -> Sem.rhs_supported supported root -> Sem.rhs_supported supported body.
Proof.
  intros H; induction H; intro Hroot; [exact Hroot| | |];
    specialize (IHprefix Hroot); inversion IHprefix; subst; auto.
Qed.
Lemma observe_ranked_cases st target x : ranked (R.observe st target) x -> ranked st x \/ x = target.
Proof.
  intros [n Hlookup]; destruct (V.eq_dec x target) as [->|Hneq]; [now right|].
  destruct (Ranks.lookup (R.ranking st) x) as [oldRank|] eqn:Hx; [left; exists oldRank; exact Hx|].
  unfold R.observe in Hlookup; destruct (Ranks.observe (R.ranking st) target) as [order rank] eqn:E.
  destruct (Ranks.lookup (R.ranking st) target) as [existing|] eqn:Ht.
  - pose proof (@RankLaws.observe_existing (R.ranking st) target existing Ht) as Hsame; change (Ranks.observe (R.ranking st) target = (R.ranking st,existing)) in Hsame; rewrite E in Hsame; inversion Hsame; subst;
      cbn in Hlookup; rewrite Hx in Hlookup; discriminate.
  - pose proof (@RankLaws.observe_fresh_preserves_absent (R.ranking st) target order rank x Ht E Hneq Hx) as Hnone.
    change (Ranks.lookup order x = None) in Hnone; change (Ranks.lookup order x = Some n) in Hlookup;
    rewrite Hnone in Hlookup; discriminate.
Qed.
Lemma materialize_ranking st target : R.ranking (R.materialize st target) = R.ranking st.
Proof. unfold R.materialize; destruct (M.lookup _ _); reflexivity. Qed.
Lemma complete_get_ranking st fr target next next_fr value :
  R.complete_get st fr target = (next,next_fr,value) -> R.ranking next = R.ranking st.
Proof.
  unfold R.complete_get; intro H; inversion H; subst; rewrite materialize_ranking;
    destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
Qed.
Lemma dirty_get_ranking tf st fr target next next_fr value :
  R.dirty_complete_get tf st fr target = (next,next_fr,value) -> R.ranking next = R.ranking st.
Proof.
  unfold R.dirty_complete_get.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  set (prepared := R.materialize base target).
  assert (Hprepared : R.ranking prepared = R.ranking st).
  { unfold prepared; rewrite materialize_ranking; unfold base; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity. }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:E;
    intro H; inversion H; subst; cbn.
  - rewrite (@dirty_result_rank tf prepared (R.frame_owner fr) target s E); exact Hprepared.
  - exact Hprepared.
Qed.
Lemma reset_ranking st owner : R.ranking (R.reset_registered_cells st owner) = R.ranking st.
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity. Qed.
Definition exposed ctrl := match ctrl with
  | R.RunSeeds (target :: _) => [target]
  | R.RunRhs _ (R.ConstraintSystem.Get target _) _ | R.RunRhs _ (R.ConstraintSystem.Side target _ _) _ |
      R.RunRhs _ (R.ConstraintSystem.Spawn target _) _ => [target]
  | _ => [] end.
Definition ranking_supported (supported : V.t -> Prop) st := forall x, ranked st x -> supported x.
Definition schedule_supported supported c :=
  Forall supported (seed_owners (R.cfg_control c)) /\ Forall supported (R.pending_spawns (R.cfg_state c)).
Lemma ranking_supported_same supported before after : R.ranking after = R.ranking before ->
  ranking_supported supported before -> ranking_supported supported after.
Proof. intros E H x Hx; apply H; unfold ranked in *; now rewrite E in Hx. Qed.
Lemma ranking_supported_observe supported st target : ranking_supported supported st -> supported target ->
  ranking_supported supported (R.observe st target).
Proof. intros H Ht x Hx; apply observe_ranked_cases in Hx as [Hx|E]; [now apply H|subst x; exact Ht]. Qed.
Lemma evaluation_supported tf roots support c fr body :
  (forall owner, In owner support -> Sem.rhs_supported (fun x => In x support) (tf owner)) ->
  ranking_supported (fun x => In x support) (R.cfg_state c) ->
  invariant tf roots c -> In (R.frame_owner fr) (active_owners (R.cfg_control c)) ->
  evaluation tf c fr body -> Sem.rhs_supported (fun x => In x support) body.
Proof.
  intros Hsys Hrank Hinv Hactive [reads [sides [spawns [Hp _]]]]; eapply prefix_supported;
    [exact Hp|apply Hsys, Hrank].
  exact (proj1 (Forall_forall _ _) (shape_stack_ranks (inv_shape Hinv)) _ Hactive).
Qed.
Lemma exposed_supported tf roots support c :
  (forall owner, In owner support -> Sem.rhs_supported (fun x => In x support) (tf owner)) ->
  ranking_supported (fun x => In x support) (R.cfg_state c) -> schedule_supported (fun x => In x support) c ->
  invariant tf roots c -> Forall (fun x => In x support) (exposed (R.cfg_control c)).
Proof.
  intros Hsys Hrank [Hseeds Hfifo] Hinv; destruct c as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k]; cbn [exposed R.cfg_control];
    try constructor.
  - destruct seeds as [|owner tail]; [constructor|]; change (Forall (fun x => In x support) (owner::tail)) in Hseeds;
      inversion Hseeds; constructor; [assumption|constructor].
  - destruct body as [direct|target tail|target raw tail|target tail]; [constructor| | |].
    all: destruct (inv_control Hinv) as [He Hk];
      pose proof (@evaluation_supported tf roots support (configuration st (R.RunRhs fr _ k)) fr _
        Hsys Hrank Hinv (or_introl eq_refl) He) as Hsupported;
      inversion Hsupported; constructor; [assumption|constructor].
Qed.

Lemma request_ranking st target : R.ranking (R.request_spawn st target) = R.ranking st.
Proof. unfold R.request_spawn; destruct (S.mem target (R.requested_spawns st)); reflexivity. Qed.
Lemma enqueue_ranking st target : R.ranking (R.enqueue st target) = R.ranking st.
Proof. reflexivity. Qed.
Lemma mark_ranking st target : R.ranking (R.mark_side_dirty st target) = R.ranking st.
Proof. reflexivity. Qed.
Lemma clear_ranking st target : R.ranking (R.clear_side_dirty st target) = R.ranking st.
Proof. reflexivity. Qed.
Lemma materialize_pending st target : R.pending_spawns (R.materialize st target) = R.pending_spawns st.
Proof. unfold R.materialize; destruct (M.lookup _ _); reflexivity. Qed.
Lemma observe_pending st target : R.pending_spawns (R.observe st target) = R.pending_spawns st.
Proof. unfold R.observe; destruct (Ranks.observe _ _); reflexivity. Qed.
Lemma reset_pending st owner : R.pending_spawns (R.reset_registered_cells st owner) = R.pending_spawns st.
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity. Qed.
Lemma enqueue_pending st target : R.pending_spawns (R.enqueue st target) = R.pending_spawns st.
Proof. reflexivity. Qed.
Lemma mark_pending st target : R.pending_spawns (R.mark_side_dirty st target) = R.pending_spawns st.
Proof. reflexivity. Qed.
Lemma clear_pending st target : R.pending_spawns (R.clear_side_dirty st target) = R.pending_spawns st.
Proof. reflexivity. Qed.
Lemma complete_get_pending st fr target next next_fr value :
  R.complete_get st fr target = (next,next_fr,value) -> R.pending_spawns next = R.pending_spawns st.
Proof.
  unfold R.complete_get; intro H; inversion H; subst; rewrite materialize_pending;
    destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
Qed.
Lemma dirty_result_pending tf st owner target next : R.try_dirty_read tf st owner target = Some next ->
  R.pending_spawns next = R.pending_spawns st.
Proof.
  intro H; destruct (@dirty_read_result tf st owner target next H) as [direct [value [_ [_ [-> _]]]]].
  destruct value; reflexivity.
Qed.
Lemma dirty_get_pending tf st fr target next next_fr value :
  R.dirty_complete_get tf st fr target = (next,next_fr,value) -> R.pending_spawns next = R.pending_spawns st.
Proof.
  unfold R.dirty_complete_get.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  set (prepared := R.materialize base target).
  assert (Hprepared : R.pending_spawns prepared = R.pending_spawns st).
  { unfold prepared; rewrite materialize_pending; unfold base; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity. }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:E; intro H; inversion H; subst; cbn.
  - rewrite (@dirty_result_pending tf prepared (R.frame_owner fr) target s E); exact Hprepared.
  - exact Hprepared.
Qed.

Ltac inspect_machine_step Hstep :=
  cbn [R.record_side_input] in Hstep;
  repeat first
    [ match type of Hstep with context [R.complete_get ?base ?fr ?target] =>
        let E := fresh "Eget" in let Hr := fresh "Hrank_get" in
        destruct (R.complete_get base fr target) as [[? ?] ?] eqn:E;
        pose proof (@complete_get_ranking base fr target _ _ _ E) as Hr;
        let Hp := fresh "Hpending_get" in pose proof (@complete_get_pending base fr target _ _ _ E) as Hp end
    | match type of Hstep with context [R.dirty_complete_get ?tf ?base ?fr ?target] =>
        let E := fresh "Eget" in let Hr := fresh "Hrank_get" in
        destruct (R.dirty_complete_get tf base fr target) as [[? ?] ?] eqn:E;
        pose proof (@dirty_get_ranking tf base fr target _ _ _ E) as Hr;
        let Hp := fresh "Hpending_get" in pose proof (@dirty_get_pending tf base fr target _ _ _ E) as Hp end
    | match type of Hstep with context [R.set_value ?base ?fr ?direct] =>
        let E := fresh "Eset" in let Hr := fresh "Hrank_set" in
        destruct (R.set_value base fr direct) as [? ?] eqn:E;
        pose proof (proj1 (@set_value_metadata base fr direct _ _ E)) as Hr;
        let Hp := fresh "Hpending_set" in pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (@set_value_metadata base fr direct _ _ E)))))) as Hp end
    | match type of Hstep with context [R.write_side_contribution ?base ?fr ?target ?input] =>
        let E := fresh "Eside" in let Hr := fresh "Hrank_side" in
        destruct (R.write_side_contribution base fr target input) as [? ?] eqn:E;
        pose proof (proj1 (proj2 (@side_write_metadata base fr target input _ _ E))) as Hr;
        let Hp := fresh "Hpending_side" in pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@side_write_metadata base fr target input _ _ E)))))))) as Hp end
    | match type of Hstep with context [if ?test then _ else _] => destruct test eqn:? end
    | match type of Hstep with context [R.queue_pop (R.queue ?st)] =>
        destruct (R.queue st) as [|? ?] eqn:?; cbn [R.queue_pop R.queue_peek] in Hstep end
    | match type of Hstep with context [R.queue_peek (R.queue ?st)] =>
        destruct (R.queue st) as [|? ?] eqn:?; cbn [R.queue_pop R.queue_peek] in Hstep end
    | match type of Hstep with context [match R.pending_spawns ?st with _ => _ end] =>
        destruct (R.pending_spawns st) as [|? ?] eqn:? end
    | progress unfold R.continue_side,R.continue_dead in Hstep ].
Ltac inspect_rank_transition Hstep :=
  inspect_machine_step Hstep;
  try discriminate; inversion Hstep; subst;
  cbn [R.cfg_state R.cfg_control exposed R.clear_side_dirty R.mark_side_dirty R.with_dirty_side_targets
    R.enqueue R.enqueue_all R.flush_deferred R.with_queue R.with_deferred_wakes];
  repeat first [progress cbn [R.enqueue R.enqueue_all R.flush_deferred R.with_queue R.with_deferred_wakes
      R.mark_side_dirty R.clear_side_dirty R.with_dirty_side_targets] |
    progress rewrite enqueue_ranking | progress rewrite mark_ranking | progress rewrite clear_ranking |
    progress rewrite materialize_ranking | progress rewrite reset_ranking |
    progress rewrite request_ranking | match goal with E : R.ranking ?a = R.ranking ?b |- _ => progress rewrite E end];
  repeat match goal with |- context [if ?test then _ else _] => destruct test eqn:? end;
  first [left; reflexivity | right; eexists; split; [now left|reflexivity]].
Lemma ranking_step_view tf before after : R.next_config tf before = Some after ->
  R.ranking (R.cfg_state after) = R.ranking (R.cfg_state before) \/
  exists target, In target (exposed (R.cfg_control before)) /\
    R.ranking (R.cfg_state after) = R.ranking (R.observe (R.cfg_state before) target).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    unfold R.next_config; cbn [R.cfg_state R.cfg_control]; intro Hstep.
  - inspect_rank_transition Hstep.
  - destruct seeds; inspect_rank_transition Hstep.
  - inspect_rank_transition Hstep.
  - inversion Hstep; subst; left; change (R.ranking (R.materialize st owner) = R.ranking st); apply materialize_ranking.
  - destruct body; inspect_rank_transition Hstep.
  - destruct pending; inspect_rank_transition Hstep.
  - inspect_rank_transition Hstep.
  - inspect_rank_transition Hstep.
  - destruct k; inspect_rank_transition Hstep.
Qed.
Lemma ranking_supported_step supported tf before after :
  R.next_config tf before = Some after -> ranking_supported supported (R.cfg_state before) ->
  Forall supported (exposed (R.cfg_control before)) -> ranking_supported supported (R.cfg_state after).
Proof.
  intros Hstep Hknown Hexposed; destruct (@ranking_step_view tf before after Hstep) as [E|[target [Hin E]]].
  - exact (@ranking_supported_same supported _ _ E Hknown).
  - apply (@ranking_supported_same supported (R.observe (R.cfg_state before) target) _ E).
    apply ranking_supported_observe; [exact Hknown|exact (proj1 (Forall_forall _ _) Hexposed target Hin)].
Qed.

Lemma with_spawns_pending st pending requested : R.pending_spawns (R.with_spawns st pending requested) = pending.
Proof. reflexivity. Qed.
Lemma with_queue_pending st queue : R.pending_spawns (R.with_queue st queue) = R.pending_spawns st.
Proof. reflexivity. Qed.
Lemma flush_pending_spawns st : R.pending_spawns (R.flush_deferred st) = R.pending_spawns st.
Proof. reflexivity. Qed.
Ltac inspect_schedule_transition Hstep :=
  try unfold R.request_spawn in Hstep;
  inspect_machine_step Hstep;
  try discriminate; inversion Hstep; subst;
  cbn [R.cfg_state R.cfg_control seed_owners suspended_seeds exposed];
  repeat first [progress rewrite materialize_pending | progress rewrite observe_pending |
    progress rewrite reset_pending | progress rewrite enqueue_pending | progress rewrite mark_pending |
    progress rewrite clear_pending | progress rewrite with_spawns_pending | progress rewrite with_queue_pending |
    progress rewrite flush_pending_spawns |
    match goal with E : R.pending_spawns ?a = ?xs |- _ => progress rewrite E end];
  repeat match goal with |- context [if ?test then _ else _] => destruct test eqn:? end;
  let Horigin := fresh "Horigin" in intro Horigin; cbn in Horigin |- *;
  repeat first [progress rewrite materialize_pending in Horigin | progress rewrite observe_pending in Horigin |
    progress rewrite reset_pending in Horigin | progress rewrite enqueue_pending in Horigin |
    progress rewrite mark_pending in Horigin | progress rewrite clear_pending in Horigin];
  repeat rewrite in_app_iff in Horigin; cbn in Horigin;
  repeat match goal with H : In _ (_ ++ _) |- _ => apply in_app_iff in H end;
  intuition congruence.
Lemma schedule_step_origin tf before after : R.next_config tf before = Some after -> forall x,
  In x (seed_owners (R.cfg_control after)) \/ In x (R.pending_spawns (R.cfg_state after)) ->
  In x (seed_owners (R.cfg_control before)) \/ In x (R.pending_spawns (R.cfg_state before)) \/
    In x (exposed (R.cfg_control before)).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    unfold R.next_config; cbn [R.cfg_state R.cfg_control]; intro Hstep; intro x.
  - inspect_schedule_transition Hstep.
  - destruct seeds; inspect_schedule_transition Hstep.
  - inspect_schedule_transition Hstep.
  - inspect_schedule_transition Hstep.
  - destruct body; inspect_schedule_transition Hstep.
  - destruct pending; inspect_schedule_transition Hstep.
  - inspect_schedule_transition Hstep.
  - inspect_schedule_transition Hstep.
  - destruct k; inspect_schedule_transition Hstep.
Qed.
Lemma schedule_supported_step supported tf before after :
  R.next_config tf before = Some after -> schedule_supported supported before ->
  Forall supported (exposed (R.cfg_control before)) -> schedule_supported supported after.
Proof.
  intros Hstep [Hs Hf] He; split; apply Forall_forall; intros x H.
  all: pose proof (@schedule_step_origin tf before after Hstep x ltac:(first [left; exact H|right; exact H])) as Horigin;
    destruct Horigin as [Hin|[Hin|Hin]];
    [exact (proj1 (Forall_forall _ _) Hs x Hin)|exact (proj1 (Forall_forall _ _) Hf x Hin)|
     exact (proj1 (Forall_forall _ _) He x Hin)].
Qed.
Lemma reachable_support tf roots (finite : Sem.finite_system tf roots) c :
  Sem.steps tf (R.initial_config roots) c ->
  ranking_supported (fun x => In x (Sem.support finite)) (R.cfg_state c) /\
  schedule_supported (fun x => In x (Sem.support finite)) c.
Proof.
  intro Hpath.
  assert (Hinitial : ranking_supported (fun x => In x (Sem.support finite))
    (R.cfg_state (R.initial_config roots)) /\ schedule_supported (fun x => In x (Sem.support finite)) (R.initial_config roots)).
  { split.
    - intros x [n H]; change (Ranks.lookup [] x = Some n) in H; discriminate.
    - split; [apply Forall_forall; intros x H; now apply (Sem.initial_supported finite)|constructor]. }
  assert (Hstep : forall first next, Sem.steps tf (R.initial_config roots) first -> Sem.step tf first next ->
    ranking_supported (fun x => In x (Sem.support finite)) (R.cfg_state first) /\
    schedule_supported (fun x => In x (Sem.support finite)) first ->
    ranking_supported (fun x => In x (Sem.support finite)) (R.cfg_state next) /\
    schedule_supported (fun x => In x (Sem.support finite)) next).
  { intros first next Hr Hs [Hranking Hschedule].
    pose proof (proj2 (@reachable_invariants tf roots first Hr)) as Hinv.
    pose proof (@exposed_supported tf roots (Sem.support finite) first (Sem.system_supported finite)
      Hranking Hschedule Hinv) as Hexposed; split;
      [exact (@ranking_supported_step _ tf first next Hs Hranking Hexposed)|
       exact (@schedule_supported_step _ tf first next Hs Hschedule Hexposed)]. }
  assert (Hwalk : forall first last, Sem.steps tf first last -> Sem.steps tf (R.initial_config roots) first ->
    ranking_supported (fun x => In x (Sem.support finite)) (R.cfg_state first) /\
    schedule_supported (fun x => In x (Sem.support finite)) first ->
    ranking_supported (fun x => In x (Sem.support finite)) (R.cfg_state last) /\
    schedule_supported (fun x => In x (Sem.support finite)) last).
  { intros first last H; induction H; intros Hr Hsupport; [exact Hsupport|].
    apply IHsteps; [eapply path_extend; eassumption|exact (Hstep a b Hr H Hsupport)]. }
  exact (Hwalk _ _ Hpath (@Sem.StepsRefl tf (R.initial_config roots)) Hinitial).
Qed.

Lemma ranked_iff_in st x : ranked st x <-> In x (R.ranking st).
Proof.
  split.
  - intros [n H]; exact (@RankLaws.lookup_some_in (R.ranking st) x n H).
  - intro H; destruct (Ranks.lookup (R.ranking st) x) as [n|] eqn:E; [exists n; exact E|].
    exfalso; exact (proj1 (@RankLaws.lookup_none_not_in (R.ranking st) x) E H).
Qed.
Lemma supported_rank_count support st : RankLaws.valid (R.ranking st) ->
  ranking_supported (fun x => In x support) st -> length (R.ranking st) <= length support.
Proof.
  intros Hvalid Hsupported; apply NoDup_incl_length; [exact Hvalid|].
  intros x H; apply Hsupported; now apply ranked_iff_in.
Qed.
Lemma supported_queue_count support st owners : ranking_supported (fun x => In x support) st ->
  ranked_list st owners -> sorted_queue st owners -> length owners <= length support.
Proof.
  intros Hsupported Hr Ho; apply NoDup_incl_length; [now apply ordered_distinct with st|].
  intros x H; apply Hsupported; exact (proj1 (Forall_forall _ _) Hr x H).
Qed.
Lemma reachable_rank_bound tf roots (finite : Sem.finite_system tf roots) c x n :
  Sem.steps tf (R.initial_config roots) c -> Ranks.lookup (R.ranking (R.cfg_state c)) x = Some n ->
  n < length (Sem.support finite).
Proof.
  intros Hreach Hlookup; pose proof (proj2 (@reachable_invariants tf roots c Hreach)) as Hinv;
    pose proof (proj1 (@reachable_support tf roots finite c Hreach)) as Hsupported.
  pose proof (@supported_rank_count (Sem.support finite) (R.cfg_state c) (shape_ranks (inv_shape Hinv)) Hsupported) as Hcount.
  pose proof (@RankLaws.lookup_bound_any (R.ranking (R.cfg_state c)) x n Hlookup) as Hbound.
  change (n < length (R.ranking (R.cfg_state c))) in Hbound; lia.
Qed.
Lemma reachable_work_counts tf roots (finite : Sem.finite_system tf roots) c :
  Sem.steps tf (R.initial_config roots) c ->
  length (R.queue (R.cfg_state c)) <= length (Sem.support finite) /\
  length (R.deferred_wakes (R.cfg_state c)) <= length (Sem.support finite) /\
  length (active_owners (R.cfg_control c)) <= length (Sem.support finite).
Proof.
  intro Hreach; pose proof (proj2 (@reachable_invariants tf roots c Hreach)) as Hinv;
    pose proof (proj1 (@reachable_support tf roots finite c Hreach)) as Hsupported.
  split.
  - exact (@supported_queue_count _ _ _ Hsupported
      (shape_queue_ranks (inv_shape Hinv)) (shape_queue_order (inv_shape Hinv))).
  - split.
    + exact (@supported_queue_count _ _ _ Hsupported
        (shape_wake_ranks (inv_shape Hinv)) (shape_wake_order (inv_shape Hinv))).
    + exact (@supported_queue_count _ _ _ Hsupported
        (shape_stack_ranks (inv_shape Hinv)) (shape_stack_order (inv_shape Hinv))).
Qed.

(** Resetting a child episode cannot replenish credits attached to a parent.
    Scopes are checked against the same discovery order as the work queues. *)
Lemma rank_lt_ranked st x y : R.rank_lt st x y = true -> ranked st x /\ ranked st y.
Proof.
  unfold R.rank_lt,R.ranking_lt,ranked.
  destruct (Ranks.lookup (R.ranking st) x) as [nx|] eqn:Hx;
    destruct (Ranks.lookup (R.ranking st) y) as [ny|] eqn:Hy; try discriminate.
  intros _; split; eauto.
Qed.
Lemma rank_lt_trans st x y z : R.rank_lt st x y = true -> R.rank_lt st y z = true -> R.rank_lt st x z = true.
Proof.
  intros Hxy Hyz; destruct (@rank_lt_ranked st x y Hxy) as [Hx Hy];
    destruct (@rank_lt_ranked st y z Hyz) as [_ Hz].
  apply (proj2 (@compare_rank st x z Hx Hz)).
  pose proof (proj1 (@compare_rank st x y Hx Hy) Hxy);
    pose proof (proj1 (@compare_rank st y z Hy Hz) Hyz); lia.
Qed.
Lemma step_rank_extension tf before after : Sem.step tf before after -> rank_extension (R.cfg_state before) (R.cfg_state after).
Proof.
  intro H; destruct (@ranking_step_view tf before after H) as [E|[target [_ E]]].
  - intros x n Hx; now rewrite E.
  - intros x n Hx; rewrite E; exact (@observe_extends (R.cfg_state before) target x n Hx).
Qed.
Lemma path_rank_extension tf before after : Sem.steps tf before after -> rank_extension (R.cfg_state before) (R.cfg_state after).
Proof. intro H; induction H; [apply rank_extension_refl|eapply rank_extension_trans; [exact (@step_rank_extension tf a b H)|exact IHsteps]]. Qed.
Definition scope_le st x y := x = y \/ R.rank_lt st x y = true.
Lemma scope_le_trans st x y z : scope_le st x y -> scope_le st y z -> scope_le st x z.
Proof. intros [->|H] [->|H']; unfold scope_le; eauto using rank_lt_trans. Qed.
Lemma scope_le_extension before after x y : rank_extension before after -> scope_le before x y -> scope_le after x y.
Proof. intros H [E|Hlt]; [now left|right; exact (@rank_lt_extension before after x y H Hlt)]. Qed.
Definition frame_scoped st fr := scope_le st (R.frame_min_scope fr) (R.frame_owner fr).
Fixpoint suspended_frames k : list R.frame :=
  match k with
  | R.KLoop | R.KSeedLoop _ => []
  | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest
  | R.KDead fr _ _ rest | R.KDrain fr rest => fr :: suspended_frames rest
  end.
Definition live_frames ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => []
  | R.StartEpisode _ k | R.Return k => suspended_frames k
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k => fr :: suspended_frames k
  end.
Definition frames_scoped st ctrl := Forall (frame_scoped st) (live_frames ctrl).
Definition reset_ids_safe st table := forall scope source target,
  In (source,target) (R.lookup_reset_ids table scope) -> scope_le st scope source /\ R.rank_lt st scope target = true.
Definition resets_scoped st := reset_ids_safe st (R.reset_at_close st).
Definition scopes_valid c := resets_scoped (R.cfg_state c) /\ frames_scoped (R.cfg_state c) (R.cfg_control c).
Lemma frames_scoped_extension before after frames : rank_extension before after ->
  Forall (frame_scoped before) frames -> Forall (frame_scoped after) frames.
Proof. intros H; apply Forall_impl; intros fr Hfr; exact (@scope_le_extension before after _ _ H Hfr). Qed.
Lemma resets_scoped_layout before after : rank_extension before after -> R.reset_at_close after = R.reset_at_close before ->
  resets_scoped before -> resets_scoped after.
Proof.
  intros Hrank Hreset H scope source target Hin; rewrite Hreset in Hin.
  destruct (H scope source target Hin) as [Hs Ht]; split;
    [exact (@scope_le_extension before after scope source Hrank Hs)|exact (@rank_lt_extension before after scope target Hrank Ht)].
Qed.
Lemma reset_lookup_update table scope ids x : R.lookup_reset_ids (M.update table scope ids) x =
  if V.eq_dec x scope then ids else R.lookup_reset_ids table x.
Proof.
  unfold R.lookup_reset_ids; destruct (V.eq_dec x scope) as [->|Hneq];
    [rewrite ML.lookup_update_same|rewrite ML.lookup_update_other by assumption]; reflexivity.
Qed.
Lemma remove_id_members id ids x : In x (R.remove_cell_id id ids) -> In x ids.
Proof. induction ids; cbn; [tauto|]; destruct (R.cell_id_eq_dec id a); cbn; intuition. Qed.
Lemma add_id_members id ids x : In x (R.add_cell_id id ids) -> x = id \/ In x ids.
Proof. unfold R.add_cell_id; destruct (in_dec R.cell_id_eq_dec id ids); cbn; intuition congruence. Qed.
Lemma safe_remove st table scope id : reset_ids_safe st table -> reset_ids_safe st (R.remove_registration table scope id).
Proof.
  intros H location source target Hin; unfold R.remove_registration in Hin; rewrite reset_lookup_update in Hin.
  destruct (V.eq_dec location scope) as [->|Hother]; eapply H; eauto using remove_id_members.
Qed.
Lemma safe_add st table scope source target : reset_ids_safe st table -> scope_le st scope source -> R.rank_lt st scope target = true ->
  reset_ids_safe st (R.add_registration table scope (source,target)).
Proof.
  intros H Hs Ht location x y Hin; unfold R.add_registration in Hin; rewrite reset_lookup_update in Hin.
  destruct (V.eq_dec location scope) as [->|Hother]; [|exact (H location x y Hin)].
  apply add_id_members in Hin as [E|Hin]; [inversion E; subst; auto|exact (H scope x y Hin)].
Qed.
Lemma register_scoped st source target scope phase : resets_scoped st -> scope_le st scope source ->
  resets_scoped (R.register_reset st source target scope phase).
Proof.
  intros H Hsource; unfold R.register_reset.
  set (requested := if Features.restart_side_phases then if R.rank_lt st scope target then Some scope else None else None).
  set (same := R.same_scope (R.side_reset_at (R.stored_side_cell st source target)) requested).
  set (without := if same then R.reset_at_close st else match R.side_reset_at (R.stored_side_cell st source target) with
    Some previous => R.remove_registration (R.reset_at_close st) previous (source,target)|None => R.reset_at_close st end).
  assert (Hwithout : reset_ids_safe st without).
  { unfold without; destruct same; [exact H|destruct (R.side_reset_at (R.stored_side_cell st source target)); auto using safe_remove]. }
  unfold resets_scoped,reset_ids_safe; cbn [R.with_cells_and_resets R.reset_at_close R.ranking R.rank_lt].
  destruct same; [exact Hwithout|]; unfold requested; destruct Features.restart_side_phases; [|exact Hwithout].
  destruct (R.rank_lt st scope target) eqn:E; [|exact Hwithout].
  exact (@safe_add st without scope source target Hwithout Hsource E).
Qed.
Lemma close_scoped st owner : resets_scoped st -> resets_scoped (R.reset_registered_cells st owner).
Proof.
  intro H; unfold R.reset_registered_cells; destruct Features.restart_side_phases; [|exact H].
  intros scope source target Hin; cbn [R.with_cells_and_resets R.reset_at_close] in Hin;
    rewrite reset_lookup_update in Hin; destruct (V.eq_dec scope owner); [contradiction|exact (H scope source target Hin)].
Qed.
Lemma frame_scope_fields st fr next_fr : R.frame_owner next_fr = R.frame_owner fr -> R.frame_min_scope next_fr = R.frame_min_scope fr ->
  frame_scoped st fr -> frame_scoped st next_fr.
Proof. intros Ho Hm H; unfold frame_scoped; now rewrite Ho,Hm. Qed.
Lemma fresh_scoped st owner phase : frame_scoped st (R.fresh_frame st owner phase).
Proof. now left. Qed.
Lemma side_frame_scoped st fr target value : frame_scoped st fr -> frame_scoped st (R.with_frame_side fr target value).
Proof. exact (fun H => H). Qed.
Lemma read_frame_scoped st fr target maximum : frame_scoped st fr ->
  frame_scoped st (R.with_frame_read fr (if R.rank_lt st target (R.frame_min_scope fr) then target else R.frame_min_scope fr) maximum).
Proof.
  intro H; unfold frame_scoped; cbn [R.with_frame_read R.frame_min_scope R.frame_owner].
  destruct (R.rank_lt st target (R.frame_min_scope fr)) eqn:E; [|exact H].
  exact (@scope_le_trans st target (R.frame_min_scope fr) (R.frame_owner fr) (or_intror E) H).
Qed.
Lemma materialize_scoped st owner : resets_scoped st -> resets_scoped (R.materialize st owner).
Proof.
  intro H; unfold R.materialize; destruct (M.lookup (R.sigma st) owner); [exact H|].
  eapply (@resets_scoped_layout st (R.with_sigma st (M.update (R.sigma st) owner D.bottom))); [intros x n Hx; exact Hx|reflexivity|exact H].
Qed.
Lemma observe_scoped st target : resets_scoped st -> resets_scoped (R.observe st target).
Proof.
  intro H; eapply (@resets_scoped_layout st _); [apply observe_extends| |exact H].
  unfold R.observe; destruct (Ranks.observe _ _); reflexivity.
Qed.
Lemma request_scoped st target : resets_scoped st -> resets_scoped (R.request_spawn st target).
Proof. unfold R.request_spawn; destruct (S.mem _ _); exact (fun H => H). Qed.
Lemma reset_get_fields st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  R.reset_at_close next = R.reset_at_close st /\ R.frame_owner next_fr = R.frame_owner fr /\
  R.frame_min_scope next_fr = if R.rank_lt st target (R.frame_min_scope fr) then target else R.frame_min_scope fr.
Proof.
  unfold R.complete_get; intro E; inversion E; subst; split; [|split; reflexivity].
  unfold R.materialize; destruct (M.lookup _ _); destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
Qed.
Lemma reset_dirty_fields tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  R.reset_at_close next = R.reset_at_close st /\ R.frame_owner next_fr = R.frame_owner fr /\
  R.frame_min_scope next_fr = if R.rank_lt st target (R.frame_min_scope fr) then target else R.frame_min_scope fr.
Proof.
  unfold R.dirty_complete_get; intro E; inversion E; subst; split; [|split; reflexivity].
  destruct (R.try_dirty_read tf _ _ target) eqn:Hdirty.
  - destruct (@dirty_read_result tf _ _ target s Hdirty) as [direct [value [_ [_ [-> _]]]]]; destruct value; unfold dirty_finish; cbn; unfold R.materialize; destruct (M.lookup _ _); destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
  - unfold R.materialize; destruct (M.lookup _ _); destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
Qed.
Lemma get_scoped st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  resets_scoped st -> frame_scoped st fr -> resets_scoped next /\ frame_scoped next next_fr.
Proof.
  intros E Hreset Hframe; destruct (@reset_get_fields st fr target next next_fr value E) as [Hr [Ho Hmin]].
  pose proof (@complete_get_ranking st fr target next next_fr value E) as Hrank.
  split.
  - eapply (@resets_scoped_layout st next); [intros x n H; now rewrite Hrank|exact Hr|exact Hreset].
  - unfold frame_scoped,scope_le; rewrite Ho,Hmin; unfold R.rank_lt; rewrite Hrank; change (scope_le st (if R.rank_lt st target (R.frame_min_scope fr) then target else R.frame_min_scope fr) (R.frame_owner fr)).
    destruct (R.rank_lt st target (R.frame_min_scope fr)) eqn:Hlt; [|exact Hframe].
    exact (@scope_le_trans st target (R.frame_min_scope fr) (R.frame_owner fr) (or_intror Hlt) Hframe).
Qed.
Lemma dirty_get_scoped tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  resets_scoped st -> frame_scoped st fr -> resets_scoped next /\ frame_scoped next next_fr.
Proof.
  intros E Hreset Hframe; destruct (@reset_dirty_fields tf st fr target next next_fr value E) as [Hr [Ho Hmin]].
  pose proof (@dirty_get_ranking tf st fr target next next_fr value E) as Hrank; split.
  - eapply (@resets_scoped_layout st next); [intros x n H; now rewrite Hrank|exact Hr|exact Hreset].
  - unfold frame_scoped,scope_le; rewrite Ho,Hmin; unfold R.rank_lt; rewrite Hrank; change (scope_le st (if R.rank_lt st target (R.frame_min_scope fr) then target else R.frame_min_scope fr) (R.frame_owner fr)).
    destruct (R.rank_lt st target (R.frame_min_scope fr)) eqn:Hlt; [|exact Hframe].
    exact (@scope_le_trans st target (R.frame_min_scope fr) (R.frame_owner fr) (or_intror Hlt) Hframe).
Qed.
Lemma write_scoped st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) ->
  resets_scoped st -> frame_scoped st fr -> resets_scoped next.
Proof.
  intros E Hreset Hframe; unfold R.write_side_contribution in E; inversion E; subst next.
  apply register_scoped.
  - unfold R.promote_side_target; destruct (R.rank_lt st target (R.frame_owner fr)); exact Hreset.
  - unfold R.promote_side_target; destruct (R.rank_lt st target (R.frame_owner fr)); exact Hframe.
Qed.
Lemma reset_set_fields st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  R.reset_at_close next = R.reset_at_close st /\ R.frame_owner next_fr = R.frame_owner fr /\
  R.frame_min_scope next_fr = R.frame_min_scope fr.
Proof.
  intro E; apply set_value_cases in E as [[_ [-> ->]]|[_ [-> [[_ ->]|[_ ->]]]]]; repeat split; reflexivity.
Qed.
Lemma commit_scoped st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  resets_scoped st -> frame_scoped st fr -> resets_scoped next /\ frame_scoped next next_fr.
Proof.
  intros E Hreset Hframe; pose proof (proj1 (@set_value_metadata st fr direct next next_fr E)) as Hrank.
  destruct (@reset_set_fields st fr direct next next_fr E) as [Hresets [Ho Hmin]].
  split; [eapply (@resets_scoped_layout st next); [intros x n H; now rewrite Hrank|exact Hresets|exact Hreset]|].
  apply (@frame_scope_fields next fr next_fr Ho Hmin); unfold frame_scoped,scope_le,R.rank_lt; rewrite Hrank; exact Hframe.
Qed.

Lemma scopes_transfer st next ctrl next_ctrl : rank_extension st next ->
  R.reset_at_close next = R.reset_at_close st -> live_frames next_ctrl = live_frames ctrl ->
  scopes_valid (configuration st ctrl) -> scopes_valid (configuration next next_ctrl).
Proof.
  intros Hr He Hframes [Hresets Hfr]; split.
  - exact (@resets_scoped_layout st next Hr He Hresets).
  - unfold frames_scoped in *; cbn [configuration R.cfg_state R.cfg_control] in *.
    rewrite Hframes; exact (@frames_scoped_extension st next _ Hr Hfr).
Qed.
Lemma scopes_same st next ctrl next_ctrl : R.ranking next = R.ranking st ->
  R.reset_at_close next = R.reset_at_close st -> live_frames next_ctrl = live_frames ctrl ->
  scopes_valid (configuration st ctrl) -> scopes_valid (configuration next next_ctrl).
Proof. intros Hr; apply scopes_transfer; intros x n H; now rewrite Hr. Qed.
Lemma scopes_observe st target ctrl : scopes_valid (configuration st ctrl) ->
  scopes_valid (configuration (R.observe st target) ctrl).
Proof.
  apply scopes_transfer; [apply observe_extends|unfold R.observe; destruct (Ranks.observe _ _); reflexivity|reflexivity].
Qed.
Lemma get_cursor_scoped dirty tf st fr target tail k :
  scopes_valid (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  scopes_valid (get_cursor dirty tf st fr target tail k).
Proof.
  intros [Hr Hframes]; change (Forall (frame_scoped st) (fr :: suspended_frames k)) in Hframes.
  pose proof (Forall_inv Hframes) as Hfr; pose proof (Forall_inv_tail Hframes) as Hk.
  unfold get_cursor; destruct dirty.
  - destruct (R.dirty_complete_get tf st fr target) as [[next next_fr] value] eqn:E.
    destruct (@dirty_get_scoped tf st fr target next next_fr value E Hr Hfr) as [Hr' Hfr']; split; [exact Hr'|].
    constructor; [exact Hfr'|]; apply (@frames_scoped_extension st next); [|exact Hk].
    intros x n H; now rewrite (@dirty_get_ranking tf st fr target next next_fr value E).
  - destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:E.
    destruct (@get_scoped st fr target next next_fr value E Hr Hfr) as [Hr' Hfr']; split; [exact Hr'|].
    constructor; [exact Hfr'|]; apply (@frames_scoped_extension st next); [|exact Hk].
    intros x n H; now rewrite (@complete_get_ranking st fr target next next_fr value E).
Qed.
Lemma observed_get_scoped dirty tf st fr target tail k :
  scopes_valid (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  scopes_valid (observed_get dirty tf st fr target tail k).
Proof.
  intro H; unfold observed_get; destruct (R.is_materialized st target); [now apply get_cursor_scoped|].
  destruct (R.rank_lt st (R.frame_owner fr) target); [exact H|].
  apply get_cursor_scoped; apply (@scopes_same st _ (R.RunRhs fr (Syntax.Get target tail) k) _); [reflexivity|reflexivity|reflexivity|exact H].
Qed.
Lemma observed_spawn_scoped st fr target tail k :
  scopes_valid (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  scopes_valid (observed_spawn st fr target tail k).
Proof.
  intro H; unfold observed_spawn; destruct (R.is_materialized st target); [exact H|].
  destruct (R.rank_lt st (R.frame_owner fr) target); [exact H|].
  apply (@scopes_same st _ (R.RunRhs fr (Syntax.Spawn target tail) k) _); [rewrite materialize_ranking; reflexivity| |reflexivity|exact H].
  unfold R.materialize; destruct (M.lookup _ _); reflexivity.
Qed.
Lemma continue_side_scoped st fr target body k changed :
  scopes_valid (configuration st (R.RunRhs fr body k)) ->
  scopes_valid (R.continue_side st fr target body k changed).
Proof.
  intro H; unfold R.continue_side; destruct changed; [|exact H].
  destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target)); [exact H|].
  apply (@scopes_same st _ (R.RunRhs fr body k) _); [reflexivity|reflexivity|reflexivity|exact H].
Qed.
Lemma continue_dead_scoped st fr direct target pending k changed :
  scopes_valid (configuration st (R.RunDead fr direct pending k)) ->
  scopes_valid (R.continue_dead st fr direct target pending k changed).
Proof.
  intro H; unfold R.continue_dead; destruct changed; [|exact H].
  destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target)); [exact H|].
  apply (@scopes_same st _ (R.RunDead fr direct pending k) _); [reflexivity|reflexivity|reflexivity|exact H].
Qed.
Lemma write_frames_scoped st next fr target input changed frames :
  R.write_side_contribution st fr target input = (next,changed) ->
  resets_scoped st -> frame_scoped st fr -> Forall (frame_scoped st) frames ->
  resets_scoped next /\ Forall (frame_scoped next) frames.
Proof.
  intros E Hr Hfr Hframes; split; [exact (@write_scoped st fr target input next changed E Hr Hfr)|].
  apply (@frames_scoped_extension st next); [|exact Hframes].
  intros x n H; now rewrite (proj1 (proj2 (@side_write_metadata st fr target input next changed E))).
Qed.
Lemma mark_frames_scoped st target frames :
  resets_scoped st /\ Forall (frame_scoped st) frames ->
  resets_scoped (R.mark_side_dirty st target) /\ Forall (frame_scoped (R.mark_side_dirty st target)) frames.
Proof. exact (fun H => H). Qed.
Lemma rhs_scopes_step tf st fr body k after :
  R.next_config tf (configuration st (R.RunRhs fr body k)) = Some after ->
  scopes_valid (configuration st (R.RunRhs fr body k)) -> scopes_valid after.
Proof.
  destruct body as [direct|target tail|target raw tail|target tail];
    unfold R.next_config,configuration; cbn [R.cfg_state R.cfg_control].
  - intros E H; inversion E; subst; exact H.
  - intros E H; destruct (R.is_dormant st target).
    + inversion E; subst; exact H.
    + pose proof (@scopes_observe st target _ H) as Hobserved.
      destruct (Ranks.lookup (R.ranking st) target).
      * rewrite ?option_cursor in E.
        assert (Eget : Some (observed_get true tf (R.observe st target) fr target tail k) = Some after).
        { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target);
            [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
        inversion Eget; subst; now apply observed_get_scoped.
      * destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)).
        -- inversion E; subst; exact H.
        -- assert (Eget : Some (observed_get false tf (R.observe st target) fr target tail k) = Some after).
           { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target);
               cbn in E; rewrite ?option_cursor in E;
               [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
           inversion Eget; subst; now apply observed_get_scoped.
  - intros E H; pose proof (@scopes_observe st target _ H) as [Hreset Hframes].
    change (Forall (frame_scoped (R.observe st target)) (fr :: suspended_frames k)) in Hframes.
    set (recorded := R.with_frame_side fr target (R.accumulated_side_input fr target raw)).
    assert (Hrecorded : Forall (frame_scoped (R.observe st target)) (recorded :: suspended_frames k)).
    { constructor; [exact (Forall_inv Hframes)|exact (Forall_inv_tail Hframes)]. }
    cbn [R.record_side_input] in E; fold recorded in E.
    destruct (R.write_side_contribution (R.observe st target) recorded target (R.accumulated_side_input fr target raw))
      as [next changed] eqn:Hwrite.
    pose proof (@write_frames_scoped (R.observe st target) next recorded target _ changed _ Hwrite Hreset (Forall_inv Hrecorded) Hrecorded) as Hpublished.
    destruct (R.is_dormant st target).
    + inversion E; subst; exact (@continue_side_scoped next recorded target tail k true Hpublished).
    + destruct changed; inversion E; subst.
      * exact (@continue_side_scoped (R.mark_side_dirty next target) recorded target tail k true (mark_frames_scoped target Hpublished)).
      * exact (@continue_side_scoped next recorded target tail k false Hpublished).
  - intros E H; destruct Features.defer_spawns.
    + inversion E; subst; apply (@scopes_same st _ (R.RunRhs fr (Syntax.Spawn target tail) k) _); [apply request_ranking|unfold R.request_spawn; destruct (S.mem _ _); reflexivity|reflexivity|exact H].
    + destruct (R.is_dormant st target); [inversion E; subst; exact H|].
      pose proof (@scopes_observe st target _ H) as Hobserved.
      destruct (Ranks.lookup (R.ranking st) target).
      * assert (Espawn : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
        { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
            [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
        inversion Espawn; subst; now apply observed_spawn_scoped.
      * destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)).
        -- inversion E; subst; exact H.
        -- assert (Espawn : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
           { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
               [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
           inversion Espawn; subst; now apply observed_spawn_scoped.
Qed.

Lemma frames_reset_scoped st owner frames : Forall (frame_scoped st) frames ->
  Forall (frame_scoped (R.reset_registered_cells st owner)) frames.
Proof.
  apply frames_scoped_extension; intros x n H; now rewrite reset_ranking.
Qed.
Lemma scopes_step tf before after : R.next_config tf before = Some after -> scopes_valid before -> scopes_valid after.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros E Hscope.
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    destruct (R.queue st) as [|owner tail]; cbn [R.queue_pop] in E.
    + destruct (R.pending_spawns st); [discriminate|]; inversion E; subst; exact Hscope.
    + inversion E; subst; exact Hscope.
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; destruct seeds as [|owner tail].
    + inversion E; subst; exact Hscope.
    + destruct (R.is_materialized st owner || R.is_dormant st owner); [inversion E; subst; exact Hscope|].
      destruct (Ranks.lookup (R.ranking st) owner).
      * inversion E; subst; exact (@scopes_observe st owner _ Hscope).
      * destruct (R.pure_bottom_rhs tf owner); inversion E; subst;
          [exact Hscope|exact (@scopes_observe st owner _ Hscope)].
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    destruct (R.queue st); cbn [R.queue_pop] in E; inversion E; subst; exact Hscope.
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; inversion E; subst.
    destruct Hscope as [Hr Hk]; split; [exact (@materialize_scoped st owner Hr)|].
    constructor; [apply fresh_scoped|].
    apply (@frames_scoped_extension st _); [|exact Hk].
    intros x n H; change (Ranks.lookup (R.ranking (R.materialize st owner)) x = Some n); now rewrite materialize_ranking.
  - exact (@rhs_scopes_step tf st fr body k after E Hscope).
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; destruct pending as [|target tail].
    + inversion E; subst; exact Hscope.
    + destruct (S.mem target (R.frame_current_targets fr)); [inversion E; subst; exact Hscope|].
      destruct Hscope as [Hr Hframes]; change (Forall (frame_scoped st) (fr :: suspended_frames k)) in Hframes.
      destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite; inversion E; subst.
      apply continue_dead_scoped.
      pose proof (@write_frames_scoped st next fr target D.bottom changed _ Hwrite Hr (Forall_inv Hframes) Hframes) as Hwritten.
      destruct changed; [exact (@mark_frames_scoped next target _ Hwritten)|exact Hwritten].
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    destruct Hscope as [Hr Hframes]; change (Forall (frame_scoped st) (fr :: suspended_frames k)) in Hframes.
    destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:Hwrite; inversion E; subst.
    destruct (@commit_scoped (R.flush_deferred st) fr direct next next_fr Hwrite Hr (Forall_inv Hframes)) as [Hr' Hfr'];
      split; [exact Hr'|]; constructor; [exact Hfr'|].
    apply (@frames_scoped_extension st next); [|exact (Forall_inv_tail Hframes)].
    intros x n H; rewrite (proj1 (@set_value_metadata (R.flush_deferred st) fr direct next next_fr Hwrite)); exact H.
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    destruct Hscope as [Hr Hframes]; change (Forall (frame_scoped st) (fr :: suspended_frames k)) in Hframes.
    destruct (R.queue st) as [|head tail]; cbn [R.queue_peek R.queue_pop] in E.
    + inversion E; subst; split; [now apply close_scoped|exact (@frames_reset_scoped st (R.frame_owner fr) _ (Forall_inv_tail Hframes))].
    + destruct (V.eq_dec head (R.frame_owner fr)) as [->|Hneq].
      * inversion E; subst; split; [exact Hr|].
        constructor; [apply fresh_scoped|exact (Forall_inv_tail Hframes)].
      * destruct (R.rank_lt st (R.frame_owner fr) head); inversion E; subst;
          [now split|split; [now apply close_scoped|exact (@frames_reset_scoped st (R.frame_owner fr) _ (Forall_inv_tail Hframes))]].
  - destruct k as [|seeds|fr target tail k|fr tail k|fr tail k|fr direct pending k|fr k];
      unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    + inversion E; subst; exact Hscope.
    + inversion E; subst; exact Hscope.
    + destruct Hscope as [Hr Hframes]; change (Forall (frame_scoped st) (fr :: suspended_frames k)) in Hframes.
      destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:Hget; inversion E; subst.
      destruct (@get_scoped st fr target next next_fr value Hget Hr (Forall_inv Hframes)) as [Hr' Hfr'];
        split; [exact Hr'|]; constructor; [exact Hfr'|].
      apply (@frames_scoped_extension st next); [|exact (Forall_inv_tail Hframes)].
      intros x n H; now rewrite (@complete_get_ranking st fr target next next_fr value Hget).
    + inversion E; subst; exact Hscope.
    + inversion E; subst; exact Hscope.
    + inversion E; subst; exact Hscope.
    + inversion E; subst; exact Hscope.
Qed.
Lemma initial_scopes roots : scopes_valid (R.initial_config roots).
Proof.
  split; [|constructor].
  intros scope source target Hin; change (In (source,target) (R.lookup_reset_ids (M.empty (list R.side_cell_id)) scope)) in Hin.
  unfold R.lookup_reset_ids in Hin; rewrite ML.lookup_empty in Hin; contradiction.
Qed.
Theorem reachable_scopes tf roots c : Sem.steps tf (R.initial_config roots) c -> scopes_valid c.
Proof.
  intro H; remember (R.initial_config roots) as first eqn:E in H.
  assert (Hfirst : scopes_valid first) by (subst first; apply initial_scopes).
  clear E; induction H; [exact Hfirst|apply IHsteps; exact (@scopes_step tf a b H Hfirst)].
Qed.

(** A higher close cannot replenish cells whose source or target is at or
    below a suspended owner. This is the reset side of the credit argument. *)
Lemma reset_cells_other ids cells source target : ~ In (source,target) ids ->
  M.lookup (R.lookup_map (R.reset_cells ids cells) source) target = M.lookup (R.lookup_map cells source) target.
Proof.
  revert cells; induction ids as [|[x y] ids IH]; intros cells H; [reflexivity|].
  cbn [R.reset_cells]; rewrite IH by (intro Hin; apply H; now right).
  unfold R.update_map,R.lookup_map.
  destruct (V.eq_dec source x) as [->|Hsource].
  - rewrite ML.lookup_update_same.
    destruct (V.eq_dec target y) as [->|Htarget]; [exfalso; apply H; now left|].
    rewrite ML.lookup_update_other by exact Htarget; reflexivity.
  - rewrite ML.lookup_update_other by exact Hsource; reflexivity.
Qed.
Lemma rank_lt_irrefl st x : R.rank_lt st x x = false.
Proof. unfold R.rank_lt,R.ranking_lt; destruct (Ranks.lookup _ _); [apply Nat.ltb_irrefl|reflexivity]. Qed.
Lemma higher_close_cell st higher source target : resets_scoped st ->
  (scope_le st source higher /\ source <> higher) \/ scope_le st target higher ->
  R.stored_side_cell (R.reset_registered_cells st higher) source target = R.stored_side_cell st source target.
Proof.
  intros Hscope Hlower; unfold R.reset_registered_cells; destruct Features.restart_side_phases; [|reflexivity].
  unfold R.stored_side_cell; cbn [R.with_cells_and_resets R.side_cells].
  rewrite reset_cells_other; [reflexivity|].
  intro Hin; destruct (Hscope higher source target Hin) as [Hs Ht].
  assert (Hself : R.rank_lt st higher higher = true).
  { destruct Hlower as [[[E|Hsh] Hneq]|[E|Hth]]; [congruence| |congruence|].
    - destruct Hs as [E|Hs]; [congruence|exact (@rank_lt_trans st higher source higher Hs Hsh)].
    - exact (@rank_lt_trans st higher target higher Ht Hth). }
  rewrite rank_lt_irrefl in Hself; discriminate.
Qed.

Lemma solved_decision st owner : {solved st owner} + {~ solved st owner}.
Proof.
  destruct (R.semantic_lookup st owner) as [value|] eqn:E.
  - left; exists value; exact E.
  - right; intros [value H]; unfold Sem.solved in H; congruence.
Qed.
Lemma unsolved_bottom st owner : ~ solved st owner -> R.sigma_value st owner = D.bottom.
Proof.
  intro H; unfold R.sigma_value; destruct (M.lookup (R.sigma st) owner) eqn:E; [|reflexivity].
  exfalso; apply H; apply solved_cases; left; eauto.
Qed.
Lemma supported_spawns supported body result : Sem.rhs_supported supported body -> Sem.rhs_observes body result ->
  forall target, In target (Sem.observed_spawns result) -> supported target.
Proof.
  intros Hsupport; revert result; induction Hsupport; intros result Htrace; inversion Htrace; subst; cbn; intros x Hin.
  - contradiction.
  - eauto.
  - eauto.
  - destruct Hin as [<-|Hin]; eauto.
Qed.
Lemma correct_observation tf roots st owner result : correct_final_state tf roots st -> solved st owner ->
  Sem.observes_at (R.sigma_value st) (tf owner) result ->
  D.leq (Sem.observed_direct result) (R.sigma_value st owner) = true /\
  Sem.valuation_side_effects_below (R.sigma_value st) (Sem.observed_sides result).
Proof.
  intros [_ Hcorrect] Howner Hobs.
  destruct (Hcorrect owner Howner) as [[direct [reads [effects Heval]]] [Hvalues _]].
  destruct (replay_observation Heval) as [saved [Htrace [Hd [Hr Hs]]]].
  assert (Hat : Sem.observes_at (R.sigma_value st) (tf owner) saved).
  { split; [exact Htrace|intros x value Hin; symmetry; apply lookup_valuation].
    change (In (x,value) (Sem.observed_reads saved)) in Hin; rewrite Hr in Hin; eapply Sem.rhs_eval_reads_lookup; eassumption. }
  pose proof (@observations_unique (R.sigma_value st) (tf owner) saved result Hat Hobs) as E; subst saved.
  destruct (Hvalues direct reads effects Heval) as [Hdirect Hsides].
  rewrite Hd, Hs; split; assumption.
Qed.
Lemma successful_post_solution fuel tf roots (finite : Sem.finite_system tf roots) final :
  source_strict_on tf (Sem.support finite) roots -> R.solve_fuel fuel tf roots = Some final ->
  Sem.post_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
  intros Hstrict Hrun; pose proof (@successful_run_correct fuel tf roots final Hrun) as Hcorrect.
  assert (Hnumeric : Strict.value_post_solution_on Sem.observes_at Sem.observed_direct Sem.observed_sides
    tf (Sem.support finite) (R.sigma_value final)).
  { eapply (@Strict.bottom_completion_is_value_post_solution Syntax.rhs Sem.observation Sem.observes_at
      Sem.observed_direct Sem.observed_sides tf (Sem.support finite) roots (R.sigma_value final) (solved final)).
    - exact (solved_decision final).
    - exact Hstrict.
    - exact (proj1 Hcorrect).
    - intros owner H; rewrite (unsolved_bottom H); apply DL.leq_refl.
    - intros owner Hin Howner result Hobs; exact (@correct_observation tf roots final owner result Hcorrect Howner Hobs). }
  intros owner Hin result Hobs; destruct (Hnumeric owner Hin result Hobs) as [Hd Hs].
  split; [exact Hd|split; [exact Hs|]].
  intros target Hspawn; exact (@supported_spawns (fun x => In x (Sem.support finite)) (tf owner) result
    (Sem.system_supported finite owner Hin) (proj1 Hobs) target Hspawn).
Qed.

(** Upper bounds are propagated through residual code, rather than through a
    second execution semantics. This keeps leastness on the shared machine. *)
Definition reads_below (upper : V.t -> D.t) events := forall x value, In (x,value) events ->
  D.leq value (upper x) = true.
Definition code_below upper owner body := forall result,
  Sem.rhs_observes body result -> reads_below upper (Sem.observed_reads result) ->
  D.leq (Sem.observed_direct result) (upper owner) = true /\
  Sem.valuation_side_effects_below upper (Sem.observed_sides result).
Lemma observation_exists values body : exists result, Sem.observes_at values body result.
Proof.
  induction body as [direct|target tail IH|target raw tail IH|target tail IH].
  - eexists; split; [constructor|intros x value H; contradiction].
  - destruct (IH (values target)) as [result [Htrace Hreads]].
    eexists; split; [econstructor; exact Htrace|].
    intros x value [H|H]; [inversion H; reflexivity|exact (Hreads x value H)].
  - destruct IH as [result [Htrace Hreads]]; eexists; split; [econstructor; exact Htrace|exact Hreads].
  - destruct IH as [result [Htrace Hreads]]; eexists; split; [econstructor; exact Htrace|exact Hreads].
Qed.
Lemma upper_code tf support upper owner : Sem.system_monotone_on tf support ->
  Sem.post_solution_on tf support upper -> In owner support -> code_below upper owner (tf owner).
Proof.
  intros Hmono Hupper Hin lower Hlower Hreads.
  destruct (observation_exists upper (tf owner)) as [higher [Hhigher Hvalues]].
  assert (Hcommon : Sem.common_read_values_le lower higher).
  { intros x low high Hl Hh; rewrite (Hvalues x high Hh); exact (Hreads x low Hl). }
  pose proof (@Sem.system_dependencies_monotone tf support Hmono owner Hin _ _ Hlower Hhigher Hcommon) as Hdeps.
  assert (Hordered : Sem.valued_events_le (Sem.observed_reads lower) (Sem.observed_reads higher)).
  { intros x low Hlow.
    assert (Hx : In x (map fst (Sem.observed_reads lower))) by (apply in_map_iff; exists (x,low); auto).
    apply Hdeps in Hx; apply in_map_iff in Hx as [[y high] [E Hhigh]]; cbn in E; subst y.
    exists high; split; [exact Hhigh|exact (Hcommon x low high Hlow Hhigh)]. }
  pose proof (@Sem.system_effects_monotone tf support Hmono owner Hin _ _ Hlower Hhigher Hordered) as Heffects.
  destruct (Hupper owner Hin higher (conj Hhigher Hvalues)) as [Hd [Hs _]].
  split; [eapply DL.leq_trans; [exact (Sem.Observation.direct_effect_le Heffects)|exact Hd]|].
  intros x low Hlow; destruct (Sem.Observation.side_effects_le Heffects x low Hlow) as [high [Hhigh Hle]].
  eapply DL.leq_trans; [exact Hle|exact (Hs x high Hhigh)].
Qed.
Lemma code_ret upper owner direct : code_below upper owner (Syntax.Ret direct) ->
  D.leq direct (upper owner) = true.
Proof. intro H; exact (proj1 (H _ (Sem.ObserveRet direct) (fun _ _ H => False_rect _ H))). Qed.
Lemma code_get upper owner target tail value : code_below upper owner (Syntax.Get target tail) ->
  D.leq value (upper target) = true -> code_below upper owner (tail value).
Proof.
  intros H Hv result Htrace Hreads; apply (H _ (@Sem.ObserveGet target value tail result Htrace)).
  intros x v [E|Hin]; [inversion E; subst; exact Hv|exact (Hreads x v Hin)].
Qed.
Lemma code_side upper owner target raw tail : code_below upper owner (Syntax.Side target raw tail) ->
  D.leq raw (upper target) = true /\ code_below upper owner tail.
Proof.
  intro H; split.
  - destruct (observation_exists upper tail) as [result [Htrace Hvalues]].
    assert (Hb : reads_below upper (Sem.observed_reads result)).
    { intros x v Hin; rewrite (Hvalues x v Hin); apply DL.leq_refl. }
    exact (proj2 (H _ (@Sem.ObserveSide target raw tail result Htrace) Hb) target raw (or_introl eq_refl)).
  - intros result Htrace Hreads; destruct (H _ (@Sem.ObserveSide target raw tail result Htrace) Hreads) as [Hd Hs].
    split; [exact Hd|intros x v Hin; apply Hs; now right].
Qed.
Lemma code_spawn upper owner target tail : code_below upper owner (Syntax.Spawn target tail) ->
  code_below upper owner tail.
Proof. intros H result Htrace Hreads; exact (H _ (@Sem.ObserveSpawn target tail result Htrace) Hreads). Qed.
Record store_below upper st := {
  upper_sigma : forall x, D.leq (R.sigma_value st x) (upper x) = true;
  upper_aggregate : forall target, D.leq (R.aggregate st target) (upper target) = true
}.
Lemma upper_cells upper st : store_below upper st -> forall source target,
  D.leq (R.stored_contribution st source target) (upper target) = true.
Proof. intros H source target; eapply DL.leq_trans; [apply contribution_le_aggregate|exact (upper_aggregate H target)]. Qed.
Definition frame_below upper fr := forall target, D.leq (local_value fr target) (upper target) = true.
Fixpoint stack_below upper k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => True
  | R.KAfterGet fr target tail rest => frame_below upper fr /\
      (forall value, D.leq value (upper target) = true -> code_below upper (R.frame_owner fr) (tail value)) /\ stack_below upper rest
  | R.KAfterSide fr tail rest | R.KAfterSpawn fr tail rest => frame_below upper fr /\
      code_below upper (R.frame_owner fr) tail /\ stack_below upper rest
  | R.KDead fr direct _ rest => frame_below upper fr /\ D.leq direct (upper (R.frame_owner fr)) = true /\ stack_below upper rest
  | R.KDrain fr rest => frame_below upper fr /\ stack_below upper rest
  end.
Definition control_below upper ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
  | R.StartEpisode _ k | R.Return k => stack_below upper k
  | R.RunRhs fr body k => frame_below upper fr /\ code_below upper (R.frame_owner fr) body /\ stack_below upper k
  | R.RunDead fr direct _ k | R.RunCommit fr direct k => frame_below upper fr /\ D.leq direct (upper (R.frame_owner fr)) = true /\ stack_below upper k
  | R.RunDrain fr k => frame_below upper fr /\ stack_below upper k
  end.
Definition config_below upper c := store_below upper (R.cfg_state c) /\ control_below upper (R.cfg_control c).
Lemma upper_layout upper before after : R.sigma after = R.sigma before ->
  R.contributions after = R.contributions before -> store_below upper before -> store_below upper after.
Proof. intros Hs Hc H; constructor; unfold R.sigma_value, R.aggregate; rewrite ?Hs, ?Hc; apply H. Qed.
Lemma upper_empty upper : store_below upper R.empty_state.
Proof.
  constructor; intros; unfold R.sigma_value, R.aggregate, R.lookup_map; cbn;
    rewrite !ML.lookup_empty; [apply DL.bottom_least|rewrite ML.values_empty; apply DL.bottom_least].
Qed.
Lemma upper_sigma_write upper st x value : store_below upper st -> D.leq value (upper x) = true ->
  store_below upper (R.with_sigma st (M.update (R.sigma st) x value)).
Proof.
  intros H Hv; constructor; [|exact (upper_aggregate H)].
  intro y; destruct (V.eq_dec x y); subst;
    [rewrite sigma_write_same; exact Hv|rewrite sigma_write_other by assumption; exact (upper_sigma H y)].
Qed.
Lemma upper_value_layout upper st next owner value : R.sigma next = M.update (R.sigma st) owner value ->
  R.contributions next = R.contributions st -> store_below upper st -> D.leq value (upper owner) = true -> store_below upper next.
Proof.
  intros Hs Hc H Hv; eapply (@upper_layout upper (R.with_sigma st (M.update (R.sigma st) owner value)) next);
    [exact Hs|exact Hc|now apply upper_sigma_write].
Qed.
Lemma upper_materialize upper st x : store_below upper st -> store_below upper (R.materialize st x).
Proof. unfold R.materialize; destruct (M.lookup _ _); auto using upper_sigma_write, DL.bottom_least. Qed.
Lemma upper_observe upper st x : store_below upper st -> store_below upper (R.observe st x).
Proof. unfold R.observe; destruct (Ranks.observe _ _); apply upper_layout; reflexivity. Qed.
Lemma upper_promote upper st x : store_below upper st -> store_below upper (R.promote_controlled st x).
Proof. apply upper_layout; reflexivity. Qed.
Lemma upper_queue upper st q : store_below upper st -> store_below upper (R.with_queue st q).
Proof. apply upper_layout; reflexivity. Qed.
Lemma upper_enqueue upper st x : store_below upper st -> store_below upper (R.enqueue st x).
Proof. apply upper_queue. Qed.
Lemma upper_readers upper st target owner : store_below upper st -> store_below upper (R.add_reader st target owner).
Proof. apply upper_layout; reflexivity. Qed.
Lemma upper_dormant upper st x : store_below upper st -> store_below upper (R.remember_dormant st x).
Proof. apply upper_layout; reflexivity. Qed.
Lemma upper_dirty upper st x : store_below upper st -> store_below upper (R.mark_side_dirty st x).
Proof. apply upper_layout; reflexivity. Qed.
Lemma upper_clear upper st x : store_below upper st -> store_below upper (R.clear_side_dirty st x).
Proof. apply upper_layout; reflexivity. Qed.
Lemma upper_cancel upper st x : store_below upper st -> store_below upper (R.cancel_dirty_target st x).
Proof. intro H; apply upper_clear, upper_queue; exact H. Qed.
Lemma upper_request upper st x : store_below upper st -> store_below upper (R.request_spawn st x).
Proof. unfold R.request_spawn; destruct (S.mem _ _); apply upper_layout; reflexivity. Qed.
Lemma upper_spawns upper st pending requested : store_below upper st -> store_below upper (R.with_spawns st pending requested).
Proof. apply upper_layout; reflexivity. Qed.
Lemma upper_flush upper st : store_below upper st -> store_below upper (R.flush_deferred st).
Proof. apply upper_layout; reflexivity. Qed.
Lemma upper_reset upper st x : store_below upper st -> store_below upper (R.reset_registered_cells st x).
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; apply upper_layout; reflexivity. Qed.
Lemma upper_targets upper st fr : store_below upper st -> store_below upper (R.publish_targets st fr).
Proof. apply upper_layout; reflexivity. Qed.
Lemma upper_fresh upper st owner phase : frame_below upper (R.fresh_frame st owner phase).
Proof. intros target; unfold local_value; cbn; rewrite ML.lookup_empty; apply DL.bottom_least. Qed.
Lemma upper_read_frame upper fr minimum maximum : frame_below upper fr -> frame_below upper (R.with_frame_read fr minimum maximum).
Proof. exact (fun H => H). Qed.
Lemma upper_phase_frame upper fr phase : frame_below upper fr -> frame_below upper (R.with_frame_phase fr phase).
Proof. exact (fun H => H). Qed.
Lemma upper_side_frame upper fr target value : frame_below upper fr -> D.leq value (upper target) = true ->
  frame_below upper (R.with_frame_side fr target value).
Proof.
  intros H Hv x; destruct (V.eq_dec target x); subst;
    [rewrite local_side_same; exact Hv|rewrite local_side_other by assumption; exact (H x)].
Qed.
Lemma upper_accumulation upper fr target raw : frame_below upper fr -> D.leq raw (upper target) = true ->
  D.leq (R.accumulated_side_input fr target raw) (upper target) = true.
Proof.
  intros H Hv; unfold R.accumulated_side_input; destruct (M.lookup (R.frame_local_side fr) target) eqn:E; [|exact Hv].
  apply join_upper; [specialize (H target); unfold local_value in H; now rewrite E in H|exact Hv].
Qed.
Lemma upper_get upper st fr target next next_fr value : store_below upper st -> frame_below upper fr ->
  R.complete_get st fr target = (next,next_fr,value) -> store_below upper next /\
  frame_below upper next_fr /\ D.leq value (upper target) = true /\ R.frame_owner next_fr = R.frame_owner fr.
Proof.
  intros Hs Hf Hget; unfold R.complete_get in Hget.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) in *.
  assert (Hb : store_below upper base) by (unfold base; destruct (R.rank_lt _ _ _); auto using upper_promote).
  inversion Hget; subst; split.
  - apply upper_materialize; eapply upper_layout with (before := base); [reflexivity|reflexivity|exact Hb].
  - split; [exact Hf|split; [|reflexivity]].
    rewrite materialize_valuation; change (D.leq (R.sigma_value base target) (upper target) = true); exact (upper_sigma Hb target).
Qed.
Lemma upper_values_update row source value bound : D.leq (R.join_values (M.values row)) bound = true ->
  D.leq value bound = true -> D.leq (R.join_values (M.values (M.update row source value))) bound = true.
Proof.
  intros Hrow Hvalue; destruct (ML.values_update row source value) as [rest [Hnew Hold]].
  apply join_values_bound; intros x Hin; apply (Permutation_in x Hnew) in Hin; destruct Hin as [<-|Hin]; [exact Hvalue|].
  apply (proj1 (join_values_bound _ _) Hrow); destruct (M.lookup row source);
    apply (Permutation_in x (Permutation_sym Hold)); [now right|exact Hin].
Qed.
Lemma upper_contribution_write upper st source target value : store_below upper st -> D.leq value (upper target) = true ->
  store_below upper (R.with_contributions st (R.update_map (R.contributions st) target source value)).
Proof.
  intros H Hv; constructor; [exact (upper_sigma H)|intros t].
  unfold R.aggregate; cbn [R.with_contributions R.contributions]; unfold R.update_map, R.lookup_map at 1.
  destruct (V.eq_dec t target) as [->|Hother].
  - rewrite ML.lookup_update_same; apply upper_values_update; [exact (upper_aggregate H target)|exact Hv].
  - rewrite ML.lookup_update_other by assumption; exact (upper_aggregate H t).
Qed.
Lemma upper_register upper st source target scope phase : store_below upper st ->
  store_below upper (R.register_reset st source target scope phase).
Proof. intro H; eapply upper_layout with (before := st); [reflexivity|reflexivity|exact H]. Qed.
Module UpperBounds (UBL : UPPER_BOUND_UPDATE_LAWS V D U) (SUBL : SIDE_UPPER_BOUND_UPDATE_LAWS V D SU).
Lemma upper_side_write upper st fr target input next changed : store_below upper st -> D.leq input (upper target) = true ->
  R.write_side_contribution st fr target input = (next,changed) -> store_below upper next.
Proof.
  intros H Hin Hwrite; unfold R.write_side_contribution in Hwrite; inversion Hwrite; subst next.
  apply upper_register, upper_contribution_write; [unfold R.promote_side_target; destruct (R.rank_lt _ _ _); auto using upper_promote|].
  apply SUBL.update_preserves_upper_bound; [|exact Hin].
  unfold R.promote_side_target; destruct (R.rank_lt _ _ _); exact (upper_cells H _ _).
Qed.
Lemma upper_commit upper st fr direct next next_fr : store_below upper st -> frame_below upper fr ->
  D.leq direct (upper (R.frame_owner fr)) = true -> R.set_value st fr direct = (next,next_fr) ->
  store_below upper next /\ frame_below upper next_fr /\ R.frame_owner next_fr = R.frame_owner fr.
Proof.
  intros Hs Hf Hd Hset; apply set_value_cases in Hset as [[_ [-> ->]]|[_ [Hfr Hresult]]]; [auto|].
  assert (Hi : D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (upper (R.frame_owner fr)) = true)
    by (apply join_upper; [exact Hd|exact (upper_aggregate Hs _)]).
  assert (Hv : D.leq (snd (if S.mem (R.frame_owner fr) (R.controlled st)
    then U.update false (R.frame_owner fr) (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
      (D.join direct (R.aggregate st (R.frame_owner fr)))
    else (R.frame_phase fr,D.join direct (R.aggregate st (R.frame_owner fr))))) (upper (R.frame_owner fr)) = true).
  { destruct (S.mem _ _); [apply UBL.update_preserves_upper_bound; [exact (upper_sigma Hs _)|exact Hi]|exact Hi]. }
  rewrite Hfr; split; [|split; [exact Hf|reflexivity]].
  destruct Hresult as [[_ ->]|[_ ->]]; [exact Hs|].
  eapply upper_value_layout; [reflexivity|reflexivity|exact Hs|exact Hv].
Qed.
Lemma upper_dirty_write upper st target value : store_below upper st -> D.leq value (upper target) = true ->
  store_below upper (R.write_dirty_value st target value).
Proof. intros H Hv; eapply upper_value_layout; [reflexivity|reflexivity|exact H|exact Hv]. Qed.
Lemma upper_dirty_read tf support upper st owner target next :
  (forall x, In x support -> code_below upper x (tf x)) -> In target support ->
  store_below upper st -> R.try_dirty_read tf st owner target = Some next -> store_below upper next.
Proof.
  intros Hcode Hin Hs Hdirty; unfold R.try_dirty_read in Hdirty.
  destruct (V.eq_dec _ _); try discriminate; destruct (R.is_side_dirty _ _); try discriminate;
    destruct (tf target) as [direct| | |] eqn:E; try discriminate;
    destruct (R.equivalent direct D.bottom); try discriminate.
  assert (Hdirect : D.leq direct (upper target) = true) by (apply code_ret; specialize (Hcode target Hin); now rewrite E in Hcode).
  assert (Hcandidate : D.leq (D.join direct (R.aggregate st target)) (upper target) = true)
    by (apply join_upper; [exact Hdirect|exact (upper_aggregate Hs target)]).
  assert (Hupdated : D.leq (snd (U.update false target (U.initial_phase false target)
    (R.sigma_value st target) (D.join direct (R.aggregate st target)))) (upper target) = true)
    by (apply UBL.update_preserves_upper_bound; [exact (upper_sigma Hs target)|exact Hcandidate]).
  repeat match type of Hdirty with context [if ?b then _ else _] => destruct b eqn:? end;
    try discriminate; inversion Hdirty; subst next; auto using upper_promote, upper_cancel, upper_dirty_write.
Qed.
Lemma upper_dirty_get tf support upper st fr target next next_fr value :
  (forall x, In x support -> code_below upper x (tf x)) -> In target support ->
  store_below upper st -> frame_below upper fr -> R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  store_below upper next /\ frame_below upper next_fr /\ D.leq value (upper target) = true /\ R.frame_owner next_fr = R.frame_owner fr.
Proof.
  intros Hcode Hin Hs Hf Hget; unfold R.dirty_complete_get in Hget.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) in *.
  set (prepared := R.materialize base target) in *.
  set (flushed := match R.try_dirty_read tf prepared (R.frame_owner fr) target with Some done => done |None => prepared end) in *.
  assert (Hb : store_below upper base) by (unfold base; destruct (R.rank_lt _ _ _); auto using upper_promote).
  assert (Hp : store_below upper prepared) by (apply upper_materialize; exact Hb).
  assert (Hd : store_below upper flushed).
  { unfold flushed; destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:E;
      [exact (@upper_dirty_read tf support upper prepared (R.frame_owner fr) target s Hcode Hin Hp E)|exact Hp]. }
  inversion Hget; subst; split; [now apply upper_readers|split; [exact Hf|split; [exact (upper_sigma Hd target)|reflexivity]]].
Qed.
Lemma upper_get_cursor dirty tf support upper st fr target tail k :
  (forall x, In x support -> code_below upper x (tf x)) -> In target support ->
  store_below upper st -> frame_below upper fr ->
  (forall value, D.leq value (upper target) = true -> code_below upper (R.frame_owner fr) (tail value)) -> stack_below upper k ->
  config_below upper (get_cursor dirty tf st fr target tail k).
Proof.
  intros Hcode Hin Hs Hf Htail Hk; unfold get_cursor; destruct dirty.
  - destruct (R.dirty_complete_get tf st fr target) as [[next next_fr] value] eqn:E.
    destruct (@upper_dirty_get tf support upper st fr target next next_fr value Hcode Hin Hs Hf E) as [Hb [Hfr [Hv Ho]]].
    split; [exact Hb|]; cbn [configuration R.cfg_control control_below]; split; [exact Hfr|split; [rewrite Ho; now apply Htail|exact Hk]].
  - destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:E.
    destruct (@upper_get upper st fr target next next_fr value Hs Hf E) as [Hb [Hfr [Hv Ho]]].
    split; [exact Hb|]; cbn [configuration R.cfg_control control_below]; split; [exact Hfr|split; [rewrite Ho; now apply Htail|exact Hk]].
Qed.
Lemma upper_observed_get dirty tf support upper st fr target tail k :
  (forall x, In x support -> code_below upper x (tf x)) -> In target support ->
  store_below upper st -> frame_below upper fr -> code_below upper (R.frame_owner fr) (Syntax.Get target tail) -> stack_below upper k ->
  config_below upper (observed_get dirty tf st fr target tail k).
Proof.
  intros Hcode Hin Hs Hf Hbody Hk.
  assert (Htail : forall value, D.leq value (upper target) = true -> code_below upper (R.frame_owner fr) (tail value))
    by (intros; eapply code_get; eassumption).
  unfold observed_get; destruct (R.is_materialized st target).
  - exact (@upper_get_cursor dirty tf support upper st fr target tail k Hcode Hin Hs Hf Htail Hk).
  - destruct (R.rank_lt st (R.frame_owner fr) target).
    + split; [exact Hs|]; cbn [configuration R.cfg_control control_below stack_below]; auto.
    + exact (@upper_get_cursor false tf support upper (R.enqueue st target) fr target tail k Hcode Hin
        (upper_enqueue target Hs) Hf Htail Hk).
Qed.
Lemma upper_observed_spawn upper st fr target tail k : store_below upper st -> frame_below upper fr ->
  code_below upper (R.frame_owner fr) tail -> stack_below upper k -> config_below upper (observed_spawn st fr target tail k).
Proof.
  intros Hs Hf Htail Hk; unfold observed_spawn; destruct (R.is_materialized st target);
    [|destruct (R.rank_lt st (R.frame_owner fr) target)]; split;
    cbn [configuration R.cfg_state R.cfg_control control_below stack_below];
    auto using upper_materialize, upper_enqueue.
Qed.
Lemma upper_continue_side upper st fr target tail k changed : store_below upper st -> frame_below upper fr ->
  code_below upper (R.frame_owner fr) tail -> stack_below upper k -> config_below upper (R.continue_side st fr target tail k changed).
Proof.
  intros Hs Hf Htail Hk; unfold R.continue_side; destruct changed;
    [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|];
    split; cbn [R.cfg_state R.cfg_control control_below stack_below]; auto using upper_enqueue.
Qed.
Lemma upper_continue_dead upper st fr direct target remaining k changed : store_below upper st -> frame_below upper fr ->
  D.leq direct (upper (R.frame_owner fr)) = true -> stack_below upper k -> config_below upper (R.continue_dead st fr direct target remaining k changed).
Proof.
  intros Hs Hf Hd Hk; unfold R.continue_dead; destruct changed;
    [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|];
    split; cbn [R.cfg_state R.cfg_control control_below stack_below]; auto using upper_enqueue.
Qed.
Lemma upper_rhs_step tf support upper st fr body k after :
  (forall x, In x support -> code_below upper x (tf x)) -> Forall (fun x => In x support) (exposed (R.RunRhs fr body k)) ->
  config_below upper (configuration st (R.RunRhs fr body k)) ->
  R.next_config tf (configuration st (R.RunRhs fr body k)) = Some after -> config_below upper after.
Proof.
  intros Hcode Hexposed [Hs [Hf [Hbody Hk]]] Hstep.
  destruct body as [direct|target tail|target raw tail|target tail];
    unfold R.next_config in Hstep; cbn [configuration R.cfg_state R.cfg_control] in Hstep.
  - inversion Hstep; subst; split; [exact Hs|].
    cbn [control_below R.cfg_control]; split; [exact Hf|split; [now apply code_ret|exact Hk]].
  - assert (Hin : In target support) by (inversion Hexposed; assumption).
    assert (Htail : forall value, D.leq value (upper target) = true -> code_below upper (R.frame_owner fr) (tail value))
      by (intros; eapply code_get; eassumption).
    destruct (R.is_dormant st target).
    + inversion Hstep; subst; split; [now apply upper_readers|].
      cbn [control_below R.cfg_control]; split; [exact Hf|split; [apply Htail; apply DL.bottom_least|exact Hk]].
    + destruct (Ranks.lookup (R.ranking st) target).
      * rewrite ?option_cursor in Hstep.
        assert (E : Some (observed_get true tf (R.observe st target) fr target tail k) = Some after).
        { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target);
            [exact Hstep|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact Hstep]. }
        inversion E; subst; exact (@upper_observed_get true tf support upper (R.observe st target) fr target tail k
          Hcode Hin (upper_observe target Hs) Hf Hbody Hk).
      * destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)).
        -- inversion Hstep; subst; split; [apply upper_readers, upper_dormant; exact Hs|].
           cbn [control_below R.cfg_control]; split; [exact Hf|split; [apply Htail; apply DL.bottom_least|exact Hk]].
        -- assert (E : Some (observed_get false tf (R.observe st target) fr target tail k) = Some after).
           { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target); cbn in Hstep; rewrite ?option_cursor in Hstep;
               [exact Hstep|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact Hstep]. }
           inversion E; subst; exact (@upper_observed_get false tf support upper (R.observe st target) fr target tail k
             Hcode Hin (upper_observe target Hs) Hf Hbody Hk).
  - destruct (@code_side upper (R.frame_owner fr) target raw tail Hbody) as [Hraw Htail].
    pose proof (@upper_accumulation upper fr target raw Hf Hraw) as Hinput.
    pose proof (@upper_side_frame upper fr target _ Hf Hinput) as Hframe.
    cbn [R.record_side_input] in Hstep.
    destruct (R.write_side_contribution (R.observe st target) (R.with_frame_side fr target (R.accumulated_side_input fr target raw))
      target (R.accumulated_side_input fr target raw)) as [next changed] eqn:E.
    pose proof (@upper_side_write upper _ _ _ _ _ _ (upper_observe target Hs) Hinput E) as Hnext.
    destruct (R.is_dormant st target).
    + inversion Hstep; subst; exact (@upper_continue_side upper next (R.with_frame_side fr target _) target tail k true Hnext Hframe Htail Hk).
    + destruct changed; inversion Hstep; subst.
      * exact (@upper_continue_side upper (R.mark_side_dirty next target) (R.with_frame_side fr target _) target tail k true
          (upper_dirty target Hnext) Hframe Htail Hk).
      * exact (@upper_continue_side upper next (R.with_frame_side fr target _) target tail k false Hnext Hframe Htail Hk).
  - pose proof (@code_spawn upper (R.frame_owner fr) target tail Hbody) as Htail.
    destruct Features.defer_spawns.
    + inversion Hstep; subst; split; [now apply upper_request|]; exact (conj Hf (conj Htail Hk)).
    + destruct (R.is_dormant st target).
      * inversion Hstep; subst; split; [exact Hs|exact (conj Hf (conj Htail Hk))].
      * destruct (Ranks.lookup (R.ranking st) target).
        -- assert (E : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
           { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
               [exact Hstep|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact Hstep]. }
           inversion E; subst; apply upper_observed_spawn; auto using upper_observe.
        -- destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)).
           ++ inversion Hstep; subst; split; [now apply upper_dormant|exact (conj Hf (conj Htail Hk))].
           ++ assert (E : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
              { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
                  [exact Hstep|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact Hstep]. }
              inversion E; subst; apply upper_observed_spawn; auto using upper_observe.
Qed.
Lemma upper_step tf roots support upper before after :
  (forall x, In x support -> code_below upper x (tf x)) ->
  ranking_supported (fun x => In x support) (R.cfg_state before) -> Forall (fun x => In x support) (exposed (R.cfg_control before)) ->
  invariant tf roots before -> config_below upper before -> Sem.step tf before after -> config_below upper after.
Proof.
  intros Hcode Hsupported Hexposed Hinv [Hs Hctrl] Hstep.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|seeds|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    cbn [R.cfg_state R.cfg_control control_below] in Hs, Hctrl, Hsupported, Hexposed;
    unfold Sem.step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  - destruct (R.queue st) as [|owner rest]; cbn [R.queue_pop] in Hstep.
    + destruct (R.pending_spawns st); try discriminate; inversion Hstep; subst; split; [now apply upper_spawns|exact I].
    + inversion Hstep; subst; split; [now apply upper_queue|exact I].
  - destruct seeds as [|owner rest]; [inversion Hstep; subst; split; [exact Hs|exact I]|].
    destruct (R.is_materialized st owner || R.is_dormant st owner);
      [|destruct (Ranks.lookup (R.ranking st) owner); [|destruct (R.pure_bottom_rhs tf owner)]];
      inversion Hstep; subst; split; cbn [R.cfg_state R.cfg_control control_below stack_below]; auto using upper_observe, upper_dormant.
  - destruct (R.queue st); cbn [R.queue_pop] in Hstep; inversion Hstep; subst; split; [exact Hs|exact I|now apply upper_queue|exact I].
  - assert (Howner : In owner support).
    { apply Hsupported; pose proof (shape_stack_ranks (inv_shape Hinv)) as Hr; now inversion Hr. }
    inversion Hstep; subst; split; [apply upper_clear,upper_materialize; exact Hs|].
    cbn [R.cfg_state R.cfg_control control_below R.frame_owner R.fresh_frame]; split; [apply upper_fresh|split; [now apply Hcode|exact Hctrl]].
  - apply (@upper_rhs_step tf support upper st fr body k after Hcode Hexposed (conj Hs Hctrl)); exact Hstep.
  - destruct Hctrl as [Hf [Hd Hk]]; destruct pending as [|target remaining].
    + inversion Hstep; subst; split; [now apply upper_targets|exact (conj Hf (conj Hd Hk))].
    + destruct (S.mem target (R.frame_current_targets fr)).
      * inversion Hstep; subst; split; [exact Hs|exact (conj Hf (conj Hd Hk))].
      * destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:E.
        pose proof (@upper_side_write upper st fr target D.bottom next changed Hs (DL.bottom_least _) E) as Hnext.
        inversion Hstep; subst; apply upper_continue_dead; auto.
        destruct changed; auto using upper_dirty.
  - destruct Hctrl as [Hf [Hd Hk]].
    destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:E.
    destruct (@upper_commit upper _ _ _ _ _ (upper_flush Hs) Hf Hd E) as [Hnext [Hframe _]].
    inversion Hstep; subst; split; [exact Hnext|exact (conj Hframe Hk)].
  - destruct Hctrl as [Hf Hk].
    assert (Howner : In (R.frame_owner fr) support).
    { apply Hsupported; pose proof (shape_stack_ranks (inv_shape Hinv)) as Hr; now inversion Hr. }
    destruct (R.queue st) as [|head rest]; cbn [R.queue_peek R.queue_pop] in Hstep.
    + inversion Hstep; subst; split; [now apply upper_reset|exact Hk].
    + destruct (V.eq_dec head (R.frame_owner fr)); [|destruct (R.rank_lt st (R.frame_owner fr) head)];
        inversion Hstep; subst.
      * split; [apply upper_clear,upper_queue; exact Hs|].
        cbn [R.cfg_state R.cfg_control control_below R.fresh_frame R.frame_owner]; split; [apply upper_fresh|split; [now apply Hcode|exact Hk]].
      * split; [now apply upper_queue|exact (conj Hf Hk)].
      * split; [now apply upper_reset|exact Hk].
  - destruct k as [|seeds|fr target tail k|fr tail k|fr tail k|fr direct pending k|fr k]; cbn [stack_below] in Hctrl.
    + inversion Hstep; subst; split; [exact Hs|exact I].
    + inversion Hstep; subst; split; [exact Hs|exact I].
    + destruct Hctrl as [Hf [Htail Hk]].
      destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:E.
      destruct (@upper_get upper st fr target next next_fr value Hs Hf E) as [Hnext [Hframe [Hv Ho]]].
      inversion Hstep; subst; split; [exact Hnext|]; cbn [R.cfg_state R.cfg_control control_below]; split; [exact Hframe|split; [rewrite Ho; now apply Htail|exact Hk]].
    + inversion Hstep; subst; split; [exact Hs|exact Hctrl].
    + inversion Hstep; subst; split; [exact Hs|exact Hctrl].
    + inversion Hstep; subst; split; [exact Hs|exact Hctrl].
    + inversion Hstep; subst; split; [exact Hs|exact Hctrl].
Qed.
Theorem reachable_upper tf roots (finite : Sem.finite_system tf roots) upper c :
  Sem.system_monotone_on tf (Sem.support finite) -> Sem.post_solution_on tf (Sem.support finite) upper ->
  Sem.steps tf (R.initial_config roots) c -> config_below upper c.
Proof.
  intros Hmono Hupper Hpath.
  assert (Hcodes : forall x, In x (Sem.support finite) -> code_below upper x (tf x)) by (intros; eapply upper_code; eassumption).
  assert (Hwalk : forall first last, Sem.steps tf first last -> Sem.steps tf (R.initial_config roots) first ->
    config_below upper first -> config_below upper last).
  { intros first last H; induction H; intros Hreach Hbound; [exact Hbound|].
    apply IHsteps; [eapply path_extend; eassumption|].
    pose proof (proj2 (@reachable_invariants tf roots a Hreach)) as Hinv.
    destruct (@reachable_support tf roots finite a Hreach) as [Hr Hschedule].
    pose proof (@exposed_supported tf roots (Sem.support finite) a (Sem.system_supported finite) Hr Hschedule Hinv) as Hexposed.
    exact (@upper_step tf roots (Sem.support finite) upper a b Hcodes Hr Hexposed Hinv Hbound H). }
  apply (Hwalk _ _ Hpath (@Sem.StepsRefl tf _) ); split; [apply upper_empty|exact I].
Qed.
Theorem successful_run_below fuel tf roots (finite : Sem.finite_system tf roots) final upper :
  Sem.system_monotone_on tf (Sem.support finite) -> Sem.post_solution_on tf (Sem.support finite) upper ->
  R.solve_fuel fuel tf roots = Some final -> forall x, D.leq (R.sigma_value final x) (upper x) = true.
Proof.
  intros Hmono Hupper Hrun; destruct (@successful_path fuel tf roots final Hrun) as [Hpath _].
  exact (upper_sigma (proj1 (@reachable_upper tf roots finite upper (Sem.terminal_config final) Hmono Hupper Hpath))).
Qed.

Theorem successful_run_least fuel tf roots (finite : Sem.finite_system tf roots) final :
  source_strict_on tf (Sem.support finite) roots -> Sem.system_monotone_on tf (Sem.support finite) ->
  R.solve_fuel fuel tf roots = Some final -> Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
  intros Hstrict Hmono Hrun; split; [exact (@successful_post_solution fuel tf roots finite final Hstrict Hrun)|].
  intros upper Hupper x Hin; exact (@successful_run_below fuel tf roots finite final upper Hmono Hupper Hrun x).
Qed.
End UpperBounds.

(** Aggregates are insensitive to map enumeration order. These facts also
    distinguish a covered join from an update that spends side credit. *)
Lemma join_values_permutation xs ys : Permutation xs ys -> eqv (R.join_values xs) (R.join_values ys).
Proof.
  intro H; split; apply join_values_bound; intros value Hin.
  - apply (proj1 (join_values_bound _ _) (DL.leq_refl _)); exact (Permutation_in value H Hin).
  - apply (proj1 (join_values_bound _ _) (DL.leq_refl _)); exact (Permutation_in value (Permutation_sym H) Hin).
Qed.
Lemma join_bottom_left value : eqv (D.join D.bottom value) value.
Proof. split; [apply join_upper; auto using DL.bottom_least,DL.leq_refl|apply DL.join_upper_right]. Qed.
Lemma row_replace_equivalent row source value :
  eqv value (match M.lookup row source with Some previous => previous|None => D.bottom end) ->
  eqv (R.join_values (M.values (M.update row source value))) (R.join_values (M.values row)).
Proof.
  intro Hvalue; destruct (ML.values_update row source value) as [rest [Hnew Hold]].
  eapply eqv_trans; [exact (join_values_permutation Hnew)|].
  destruct (M.lookup row source).
  - eapply eqv_trans; [apply join_congruent; [exact Hvalue|apply eqv_refl]|].
    apply eqv_sym; exact (join_values_permutation Hold).
  - eapply eqv_trans; [apply join_congruent; [exact Hvalue|apply eqv_refl]|].
    eapply eqv_trans; [apply join_bottom_left|apply eqv_sym; exact (join_values_permutation Hold)].
Qed.
Lemma row_replace_increasing row source value :
  D.leq (match M.lookup row source with Some previous => previous|None => D.bottom end) value = true ->
  D.leq (R.join_values (M.values row)) (R.join_values (M.values (M.update row source value))) = true.
Proof.
  intro Hvalue; destruct (ML.values_update row source value) as [rest [Hnew Hold]].
  pose proof (join_values_permutation Hnew) as Hn.
  destruct (M.lookup row source).
  - pose proof (join_values_permutation Hold) as Ho.
    eapply DL.leq_trans; [exact (proj1 Ho)|].
    eapply DL.leq_trans; [apply join_mono; [exact Hvalue|apply DL.leq_refl]|exact (proj2 Hn)].
  - pose proof (join_values_permutation Hold) as Ho.
    eapply DL.leq_trans; [exact (proj1 Ho)|].
    eapply DL.leq_trans; [apply DL.join_upper_right|exact (proj2 Hn)].
Qed.
Lemma aggregate_replace_equivalent st source target value : eqv value (R.stored_contribution st source target) ->
  eqv (R.aggregate (R.with_contributions st (R.update_map (R.contributions st) target source value)) target) (R.aggregate st target).
Proof.
  unfold R.aggregate, R.stored_contribution; intro H;
    cbn [R.with_contributions R.contributions]; unfold R.update_map, R.lookup_map at 1;
    rewrite ML.lookup_update_same; now apply row_replace_equivalent.
Qed.
Lemma aggregate_covered_join st source target input : D.leq input (R.aggregate st target) = true ->
  eqv (R.aggregate (R.with_contributions st (R.update_map (R.contributions st) target source
    (D.join (R.stored_contribution st source target) input))) target) (R.aggregate st target).
Proof.
  intro H; unfold R.aggregate at 1; cbn [R.with_contributions R.contributions]; unfold R.update_map,R.lookup_map at 1;
    rewrite ML.lookup_update_same; split.
  - apply upper_values_update; [apply DL.leq_refl|apply join_upper; [apply contribution_le_aggregate|exact H]].
  - unfold R.aggregate; apply row_replace_increasing; apply DL.join_upper_left.
Qed.
Lemma nested_lookup_update {A} (table : M.t (M.t A)) x y value source target :
  M.lookup (R.lookup_map (R.update_map table x y value) source) target =
  if V.eq_dec source x then if V.eq_dec target y then Some value
    else M.lookup (R.lookup_map table source) target
  else M.lookup (R.lookup_map table source) target.
Proof.
  unfold R.update_map,R.lookup_map; destruct (V.eq_dec source x) as [->|Hsource].
  - rewrite ML.lookup_update_same; destruct (V.eq_dec target y) as [->|Htarget];
      [rewrite ML.lookup_update_same|rewrite ML.lookup_update_other by exact Htarget]; reflexivity.
  - rewrite ML.lookup_update_other by exact Hsource; reflexivity.
Qed.
Lemma register_cell_other st source target scope phase x y : x <> source \/ y <> target ->
  R.stored_side_cell (R.register_reset st source target scope phase) x y = R.stored_side_cell st x y.
Proof.
  intro H; unfold R.register_reset,R.stored_side_cell; cbn [R.with_cells_and_resets R.side_cells].
  rewrite nested_lookup_update; destruct (V.eq_dec x source), (V.eq_dec y target); try reflexivity; intuition.
Qed.
Lemma contribution_put_other st source target value x y : x <> source \/ y <> target ->
  R.stored_contribution (R.with_contributions st (R.update_map (R.contributions st) target source value)) x y = R.stored_contribution st x y.
Proof.
  intro H; unfold R.stored_contribution; cbn [R.with_contributions R.contributions].
  rewrite nested_lookup_update; destruct (V.eq_dec y target), (V.eq_dec x source); try reflexivity; intuition.
Qed.
Lemma side_write_cells_other st fr target input next changed x y :
  R.write_side_contribution st fr target input = (next,changed) ->
  x <> R.frame_owner fr \/ y <> target ->
  R.stored_side_cell next x y = R.stored_side_cell st x y /\
  R.stored_contribution next x y = R.stored_contribution st x y.
Proof.
  intros E H; unfold R.write_side_contribution in E; inversion E; subst next; split.
  - rewrite register_cell_other by exact H.
    unfold R.stored_side_cell; cbn [R.with_contributions R.side_cells]; unfold R.promote_side_target;
      destruct (R.rank_lt _ _ _); reflexivity.
  - change (R.stored_contribution (R.with_contributions (R.promote_side_target st fr target)
      (R.update_map (R.contributions (R.promote_side_target st fr target)) target (R.frame_owner fr)
        (snd (R.side_update (R.promote_side_target st fr target) (R.frame_owner fr) target input)))) x y = R.stored_contribution st x y).
    rewrite contribution_put_other by exact H; unfold R.stored_contribution,R.promote_side_target;
      destruct (R.rank_lt _ _ _); reflexivity.
Qed.
Definition sum_nat {A} (xs : list A) (f : A -> nat) := fold_right (fun x total => f x + total) 0 xs.
Lemma sum_nat_pointwise {A} (xs : list A) before after :
  (forall x, In x xs -> after x <= before x) -> sum_nat xs after <= sum_nat xs before.
Proof. unfold sum_nat; induction xs; cbn; intros H; [lia|pose proof (H a ltac:(now left)) as Hhead; specialize (IHxs ltac:(intros x Hin; apply H; now right)); lia]. Qed.
Lemma sum_nat_strict {A} (xs : list A) before after x :
  (forall y, In y xs -> after y <= before y) -> In x xs -> after x < before x -> sum_nat xs after < sum_nat xs before.
Proof.
  unfold sum_nat; induction xs as [|y ys IH]; cbn; intros H Hin Hstrict; [contradiction|].
  pose proof (H y ltac:(now left)) as Hhead.
  assert (Htail : forall z, In z ys -> after z <= before z) by (intros; apply H; now right).
  destruct Hin as [<-|Hin].
  - pose proof (@sum_nat_pointwise A ys before after Htail); unfold sum_nat in *; lia.
  - specialize (IH Htail Hin Hstrict); lia.
Qed.
Lemma sum_nat_ext {A} (xs : list A) f g : (forall x, In x xs -> f x = g x) -> sum_nat xs f = sum_nat xs g.
Proof. unfold sum_nat; induction xs; cbn; intros H; [reflexivity|rewrite H by (now left); f_equal; apply IHxs; intros; apply H; now right]. Qed.

Module SideCredits (SUL : RESTARTING_SIDE_UPDATE_TERMINATION_LAWS V D SU).
Definition cell_credit st source target := SUL.remaining_changes
  (R.side_phase (R.stored_side_cell st source target)) (R.stored_contribution st source target).
Lemma credit_layout before after source target : R.side_cells after = R.side_cells before ->
  R.contributions after = R.contributions before -> cell_credit after source target = cell_credit before source target.
Proof. intros Hcell Hvalue; unfold cell_credit,R.stored_side_cell,R.stored_contribution; now rewrite Hcell,Hvalue. Qed.
Lemma credit_promote st fr target source written : cell_credit (R.promote_side_target st fr target) source written = cell_credit st source written.
Proof. unfold R.promote_side_target; destruct (R.rank_lt _ _ _); reflexivity. Qed.
Lemma credit_put st source target scope phase value :
  cell_credit (R.register_reset (R.with_contributions st (R.update_map (R.contributions st) target source value))
    source target scope phase) source target = SUL.remaining_changes phase value.
Proof.
  unfold cell_credit,R.stored_side_cell,R.stored_contribution,R.register_reset;
    cbn [R.with_cells_and_resets R.side_cells R.with_contributions R.contributions];
    unfold R.lookup_map,R.update_map; rewrite !ML.lookup_update_same; reflexivity.
Qed.
Lemma credit_write st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) ->
  cell_credit next (R.frame_owner fr) target <= cell_credit st (R.frame_owner fr) target /\
  (changed = true -> cell_credit next (R.frame_owner fr) target < cell_credit st (R.frame_owner fr) target).
Proof.
  intro Hwrite; unfold R.write_side_contribution in Hwrite.
  set (base := R.promote_side_target st fr target) in *.
  set (source := R.frame_owner fr) in *.
  set (phase := R.side_phase (R.stored_side_cell base source target)).
  set (old := R.stored_contribution base source target).
  set (aggregate := R.aggregate base target).
  destruct (SU.update source target phase old input aggregate) as [next_phase value] eqn:E.
  unfold R.side_update in Hwrite; fold source phase old aggregate in Hwrite; rewrite E in Hwrite; cbn in Hwrite;
    inversion Hwrite; subst next changed.
  rewrite credit_put,<- (@credit_promote st fr target source target).
  fold base; unfold cell_credit at 2; fold phase old.
  assert (Hold : D.leq old aggregate = true) by apply contribution_le_aggregate.
  pose proof (@SUL.remaining_changes_nonincreasing source target phase old input aggregate Hold) as Hcredit;
    rewrite E in Hcredit; cbn in Hcredit; split; [exact Hcredit|].
  intro Hchanged.
  assert (Hdifferent : ~ eqv value old).
  { intro Heq; pose proof (@aggregate_replace_equivalent base source target value Heq) as Hagg.
    apply equivalent_true in Hagg.
    change (negb (R.equivalent (R.aggregate (R.with_contributions base
      (R.update_map (R.contributions base) target source value)) target) (R.aggregate base target)) = true) in Hchanged.
    rewrite Hagg in Hchanged; discriminate. }
  assert (Hnoncovered : D.leq input old = true \/ D.leq input aggregate = false).
  { destruct (D.leq input old) eqn:Hi; [now left|].
    destruct (D.leq input aggregate) eqn:Ha; [|now right].
    pose proof (@SUL.covered_output_is_join source target phase old input aggregate Hi Ha) as Hv;
      rewrite E in Hv; cbn in Hv; subst value.
    pose proof (@aggregate_covered_join base source target input Ha) as Hagg; fold old in Hagg; apply equivalent_true in Hagg.
    change (negb (R.equivalent (R.aggregate (R.with_contributions base
      (R.update_map (R.contributions base) target source (D.join old input))) target) (R.aggregate base target)) = true) in Hchanged.
    rewrite Hagg in Hchanged; discriminate. }
  pose proof (@SUL.noncovered_change_consumes source target phase old input aggregate Hold Hnoncovered) as Hstrict;
    rewrite E in Hstrict; cbn in Hstrict; exact (Hstrict Hdifferent).
Qed.
Lemma credit_write_other st fr target input next changed x y :
  R.write_side_contribution st fr target input = (next,changed) ->
  x <> R.frame_owner fr \/ y <> target -> cell_credit next x y = cell_credit st x y.
Proof.
  intros E H; destruct (@side_write_cells_other st fr target input next changed x y E H) as [Hcells Hvalues].
  unfold cell_credit; now rewrite Hcells,Hvalues.
Qed.
Lemma credit_write_pointwise st fr target input next changed x y :
  R.write_side_contribution st fr target input = (next,changed) -> cell_credit next x y <= cell_credit st x y.
Proof.
  intro E; destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hx];
    destruct (V.eq_dec y target) as [->|Hy].
  - exact (proj1 (@credit_write st fr target input next changed E)).
  - rewrite (@credit_write_other st fr target input next changed _ _ E (or_intror Hy)); lia.
  - rewrite (@credit_write_other st fr target input next changed _ _ E (or_introl Hx)); lia.
  - rewrite (@credit_write_other st fr target input next changed _ _ E (or_introl Hx)); lia.
Qed.
Definition source_credit targets st source := sum_nat targets (cell_credit st source).
Definition target_credit sources st target := sum_nat sources (fun source => cell_credit st source target).
Definition side_credit sources targets st := sum_nat sources (source_credit targets st).
Lemma source_credit_write targets st fr target input next changed source :
  R.write_side_contribution st fr target input = (next,changed) ->
  source_credit targets next source <= source_credit targets st source.
Proof. intro E; apply sum_nat_pointwise; intros x _; exact (@credit_write_pointwise st fr target input next changed source x E). Qed.
Lemma target_credit_write sources st fr target input next changed written :
  R.write_side_contribution st fr target input = (next,changed) ->
  target_credit sources next written <= target_credit sources st written.
Proof. intro E; apply sum_nat_pointwise; intros x _; exact (@credit_write_pointwise st fr target input next changed x written E). Qed.
Lemma source_credit_write_strict targets st fr target input next :
  R.write_side_contribution st fr target input = (next,true) -> In target targets ->
  source_credit targets next (R.frame_owner fr) < source_credit targets st (R.frame_owner fr).
Proof.
  intros E Hin; apply (@sum_nat_strict V.t targets _ _ target); [|exact Hin|].
  - intros x _; exact (@credit_write_pointwise st fr target input next true (R.frame_owner fr) x E).
  - exact (proj2 (@credit_write st fr target input next true E) eq_refl).
Qed.
Lemma target_credit_write_strict sources st fr target input next :
  R.write_side_contribution st fr target input = (next,true) -> In (R.frame_owner fr) sources ->
  target_credit sources next target < target_credit sources st target.
Proof.
  intros E Hin; apply (@sum_nat_strict V.t sources _ _ (R.frame_owner fr)); [|exact Hin|].
  - intros x _; exact (@credit_write_pointwise st fr target input next true x target E).
  - exact (proj2 (@credit_write st fr target input next true E) eq_refl).
Qed.
Theorem side_credit_write sources targets st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  side_credit sources targets next <= side_credit sources targets st /\
  (changed = true -> In (R.frame_owner fr) sources -> In target targets ->
    side_credit sources targets next < side_credit sources targets st).
Proof.
  intro E; split.
  - apply sum_nat_pointwise; intros source _; exact (@source_credit_write targets st fr target input next changed source E).
  - intros -> Hsource Htarget; apply (@sum_nat_strict V.t sources _ _ (R.frame_owner fr)); [|exact Hsource|].
    + intros source _; exact (@source_credit_write targets st fr target input next true source E).
    + exact (@source_credit_write_strict targets st fr target input next E Htarget).
Qed.
Lemma credit_higher_close st scope source target : resets_scoped st ->
  (scope_le st source scope /\ source <> scope) \/ scope_le st target scope ->
  cell_credit (R.reset_registered_cells st scope) source target = cell_credit st source target.
Proof.
  intros Hr Hless; unfold cell_credit; rewrite (@higher_close_cell st scope source target Hr Hless).
  f_equal; unfold R.stored_contribution,R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity.
Qed.
Theorem source_credit_higher_close targets st scope source : resets_scoped st ->
  scope_le st source scope -> source <> scope ->
  source_credit targets (R.reset_registered_cells st scope) source = source_credit targets st source.
Proof.
  intros Hr Hless Hneq; apply sum_nat_ext; intros target _; apply credit_higher_close; [exact Hr|left; now split].
Qed.
Theorem target_credit_higher_close sources st scope target : resets_scoped st -> scope_le st target scope ->
  target_credit sources (R.reset_registered_cells st scope) target = target_credit sources st target.
Proof. intros Hr Hless; apply sum_nat_ext; intros source _; apply credit_higher_close; [exact Hr|now right]. Qed.
Definition dirty_potential sources st target := 2 * target_credit sources st target + if R.is_side_dirty st target then 1 else 0.
Lemma target_credit_mark sources st target written : target_credit sources (R.mark_side_dirty st written) target = target_credit sources st target.
Proof. reflexivity. Qed.
Lemma target_credit_clear sources st target written : target_credit sources (R.clear_side_dirty st written) target = target_credit sources st target.
Proof. reflexivity. Qed.
Lemma dirty_flag_mark_same st target : R.is_side_dirty (R.mark_side_dirty st target) target = true.
Proof. unfold R.is_side_dirty,R.mark_side_dirty; cbn [R.with_dirty_side_targets R.dirty_side_targets]; now rewrite ML.lookup_update_same. Qed.
Lemma dirty_flag_clear_same st target : R.is_side_dirty (R.clear_side_dirty st target) target = false.
Proof. unfold R.is_side_dirty,R.clear_side_dirty; cbn [R.with_dirty_side_targets R.dirty_side_targets]; now rewrite ML.lookup_update_same. Qed.
Lemma dirty_flag_mark_other st target written : target <> written -> R.is_side_dirty (R.mark_side_dirty st written) target = R.is_side_dirty st target.
Proof. intro H; unfold R.is_side_dirty,R.mark_side_dirty; cbn [R.with_dirty_side_targets R.dirty_side_targets]; now rewrite ML.lookup_update_other. Qed.
Lemma dirty_flag_clear_other st target written : target <> written -> R.is_side_dirty (R.clear_side_dirty st written) target = R.is_side_dirty st target.
Proof. intro H; unfold R.is_side_dirty,R.clear_side_dirty; cbn [R.with_dirty_side_targets R.dirty_side_targets]; now rewrite ML.lookup_update_other. Qed.
Theorem changed_side_spends_dirty_potential sources st fr target input next :
  R.write_side_contribution st fr target input = (next,true) -> In (R.frame_owner fr) sources ->
  dirty_potential sources (R.mark_side_dirty next target) target < dirty_potential sources st target.
Proof.
  intros E Hin; unfold dirty_potential; rewrite target_credit_mark,dirty_flag_mark_same.
  pose proof (@target_credit_write_strict sources st fr target input next E Hin);
    destruct (R.is_side_dirty st target); lia.
Qed.
Theorem clear_dirty_potential sources st target written :
  dirty_potential sources (R.clear_side_dirty st written) target <= dirty_potential sources st target /\
  (target = written -> R.is_side_dirty st target = true ->
    dirty_potential sources (R.clear_side_dirty st written) target < dirty_potential sources st target).
Proof.
  unfold dirty_potential; rewrite target_credit_clear; destruct (V.eq_dec target written) as [->|Hneq].
  - rewrite dirty_flag_clear_same; destruct (R.is_side_dirty st written); split; intros; lia.
  - rewrite dirty_flag_clear_other by exact Hneq; split; [lia|intros E; congruence].
Qed.

End SideCredits.

Module CommitCredits (OUL : ORDINARY_UPDATE_TERMINATION_LAWS V D U).
Lemma controlled_commit_credit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  S.mem (R.frame_owner fr) (R.controlled st) = true ->
  OUL.remaining_changes (R.frame_phase next_fr) (R.sigma_value next (R.frame_owner fr)) <=
  OUL.remaining_changes (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr)).
Proof.
  intros H Hcontrolled; apply set_value_cases in H as [[_ [-> ->]]|[_ [Hframe Hresult]]]; [lia|].
  rewrite Hcontrolled in Hframe, Hresult; rewrite Hframe; cbn [R.with_frame_phase R.frame_phase].
  set (owner := R.frame_owner fr); set (old := R.sigma_value st owner); set (input := D.join direct (R.aggregate st owner)); fold owner old input in Hresult |- *.
  destruct Hresult as [[Heq ->]|[_ ->]].
  - apply equivalent_true in Heq.
    fold old.
    rewrite <- (OUL.remaining_changes_extensional (fst (U.update false owner (R.frame_phase fr) old input)) Heq).
    apply OUL.remaining_changes_nonincreasing.
  - rewrite publication_value; apply OUL.remaining_changes_nonincreasing.
Qed.
Lemma changed_controlled_commit_consumes st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  S.mem (R.frame_owner fr) (R.controlled st) = true ->
  ~ eqv (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) ->
  OUL.remaining_changes (R.frame_phase next_fr) (R.sigma_value next (R.frame_owner fr)) <
  OUL.remaining_changes (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr)).
Proof.
  intros H Hcontrolled Hchanged; apply set_value_cases in H as [[_ [-> _]]|[_ [Hframe Hresult]]].
  - exfalso; apply Hchanged; apply eqv_refl.
  - rewrite Hcontrolled in Hframe, Hresult.
    destruct Hresult as [[_ ->]|[_ ->]]; [exfalso; apply Hchanged; apply eqv_refl|].
    rewrite Hframe; cbn [R.with_frame_phase R.frame_phase]; rewrite publication_value in *.
    now apply OUL.update_change_consumes.
Qed.
End CommitCredits.

(** Ordinary code leaves contribution storage empty. The frame component
    also rules out dead-side clearing, rather than assuming it away. *)
Definition set_empty xs := forall x, S.mem x xs = false.
Definition side_free_frame fr := set_empty (R.frame_current_targets fr) /\ set_empty (R.frame_previous_targets fr).
Definition side_free_store st := R.contributions st = M.empty R.contribution_row /\
  (forall x, R.is_side_dirty st x = false) /\
  (forall owner, set_empty (R.lookup_set (R.last_targets st) owner)).
Fixpoint dead_free_stack k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => True
  | R.KDead _ _ _ _ => False
  | R.KAfterGet _ _ _ rest | R.KAfterSide _ _ rest | R.KAfterSpawn _ _ rest | R.KDrain _ rest => dead_free_stack rest
  end.
Definition dead_empty ctrl := match ctrl with
  | R.RunDead _ _ pending k => pending = [] /\ dead_free_stack k
  | R.StartEpisode _ k | R.Return k | R.RunRhs _ _ k | R.RunCommit _ _ k | R.RunDrain _ k => dead_free_stack k
  | _ => True end.
Definition side_free_config c := side_free_store (R.cfg_state c) /\
  Forall side_free_frame (live_frames (R.cfg_control c)) /\ dead_empty (R.cfg_control c).
Lemma set_empty_elements xs : set_empty xs -> S.elements xs = [].
Proof.
  intro H; destruct (S.elements xs) as [|x tail] eqn:E; [reflexivity|].
  assert (S.mem x xs = true) by (apply SL.mem_spec; rewrite E; now left).
  rewrite H in H0; discriminate.
Qed.
Lemma no_side_prefix tf owner body reads sides spawns : no_side_effects tf ->
  prefix (tf owner) body reads sides spawns -> sides = [] /\ forall result,
  Sem.rhs_observes body result -> Sem.observed_sides result = [].
Proof.
  intros Hpure Hp; destruct (observation_exists (fun _ => D.bottom) body) as [result [Htrace _]].
  pose proof (Hpure owner _ (@prefix_observation (tf owner) body reads sides spawns Hp result Htrace)) as E.
  change (sides ++ Sem.observed_sides result = []) in E; apply app_eq_nil in E as [E _]; split; [exact E|].
  intros result' Htrace'; pose proof (Hpure owner _ (@prefix_observation (tf owner) body reads sides spawns Hp result' Htrace')) as E'.
  change (sides ++ Sem.observed_sides result' = []) in E'; exact (proj2 (app_eq_nil _ _ E')).
Qed.
Lemma ordinary_evaluation_sides tf c fr body : no_side_effects tf -> evaluation tf c fr body ->
  set_empty (R.frame_current_targets fr) /\ forall target raw tail, body <> Syntax.Side target raw tail.
Proof.
  intros Hpure [reads [sides [spawns [Hp [_ [_ [_ [Htargets _]]]]]]]].
  destruct (@no_side_prefix tf (R.frame_owner fr) body reads sides spawns Hpure Hp) as [-> Hresidual]; split.
  - intros x; destruct (S.mem x (R.frame_current_targets fr)) eqn:E; [|reflexivity].
    apply Htargets in E as [value Hin]; contradiction.
  - intros target raw tail E; subst body.
    destruct (observation_exists (fun _ => D.bottom) tail) as [result [Htrace _]].
    pose proof (Hresidual _ (Sem.ObserveSide target raw Htrace)); discriminate.
Qed.
Lemma side_free_fields before after : R.contributions after = R.contributions before ->
  (forall x, R.is_side_dirty after x = R.is_side_dirty before x) ->
  R.last_targets after = R.last_targets before -> side_free_store before -> side_free_store after.
Proof. intros Hc Hd Ht [Hempty [Hdirty Htargets]]; split; [now rewrite Hc|split; [intros x; now rewrite Hd|now rewrite Ht]]. Qed.
Lemma side_free_materialize st target : side_free_store st -> side_free_store (R.materialize st target).
Proof. unfold R.materialize; destruct (M.lookup _ _); exact (fun H => H). Qed.
Lemma side_free_observe st target : side_free_store st -> side_free_store (R.observe st target).
Proof. unfold R.observe; destruct (Ranks.observe _ _); exact (fun H => H). Qed.
Lemma side_free_request st target : side_free_store st -> side_free_store (R.request_spawn st target).
Proof. unfold R.request_spawn; destruct (S.mem _ _); exact (fun H => H). Qed.
Lemma side_free_reset st target : side_free_store st -> side_free_store (R.reset_registered_cells st target).
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; exact (fun H => H). Qed.
Lemma side_free_clear st target : side_free_store st -> side_free_store (R.clear_side_dirty st target).
Proof.
  intros [Hc [Hd Ht]]; split; [exact Hc|split; [|exact Ht]].
  intros x; destruct (V.eq_dec x target) as [->|Hneq].
  - unfold R.is_side_dirty,R.clear_side_dirty; cbn [R.with_dirty_side_targets R.dirty_side_targets]; now rewrite ML.lookup_update_same.
  - unfold R.is_side_dirty,R.clear_side_dirty; cbn [R.with_dirty_side_targets R.dirty_side_targets]; rewrite ML.lookup_update_other by exact Hneq; apply Hd.
Qed.
Lemma side_free_fresh st owner phase : side_free_store st -> side_free_frame (R.fresh_frame st owner phase).
Proof. intros [_ [_ H]]; split; [intros x; apply SL.empty_spec|exact (H owner)]. Qed.
Lemma side_free_publish st fr : side_free_store st -> side_free_frame fr -> side_free_store (R.publish_targets st fr).
Proof.
  intros [Hc [Hd Ht]] [Hcurrent Hprevious]; split; [exact Hc|split; [exact Hd|]].
  intros owner x; unfold R.publish_targets,R.lookup_set; cbn.
  destruct (V.eq_dec owner (R.frame_owner fr)) as [->|Hneq].
  - rewrite ML.lookup_update_same; exact (Hcurrent x).
  - rewrite ML.lookup_update_other by exact Hneq; exact (Ht owner x).
Qed.
Lemma side_free_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  side_free_store st -> side_free_frame fr -> side_free_store next /\ side_free_frame next_fr.
Proof.
  unfold R.complete_get; intro E; inversion E; subst.
  intros Hs Hfr; split; [|exact Hfr].
  apply side_free_materialize; destruct (R.rank_lt st (R.frame_owner fr) target); exact Hs.
Qed.
Lemma side_free_dirty_get tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  side_free_store st -> side_free_frame fr -> side_free_store next /\ side_free_frame next_fr.
Proof.
  intros E Hs Hfr; unfold R.dirty_complete_get in E.
  assert (Hprepared : side_free_store (R.materialize (if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) target)).
  { apply side_free_materialize; destruct (R.rank_lt st (R.frame_owner fr) target); exact Hs. }
  unfold R.try_dirty_read in E; destruct (V.eq_dec (R.frame_owner fr) target);
    [|rewrite (proj1 (proj2 Hprepared)) in E]; inversion E; subst.
  all: split; [exact Hprepared|exact Hfr].
Qed.
Lemma side_free_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  side_free_store st -> side_free_frame fr -> side_free_store next /\ side_free_frame next_fr.
Proof.
  intros E Hs Hfr; apply set_value_cases in E as [[_ [-> ->]]|[_ [-> [[_ ->]|[_ ->]]]]]; now split.
Qed.
Lemma side_free_cursor dirty tf st fr target tail k :
  side_free_config (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  side_free_config (get_cursor dirty tf st fr target tail k).
Proof.
  intros [Hs [Hframes Hdead]]; change (Forall side_free_frame (fr :: suspended_frames k)) in Hframes.
  unfold get_cursor; destruct dirty.
  - destruct (R.dirty_complete_get tf st fr target) as [[next next_fr] value] eqn:E.
    destruct (@side_free_dirty_get tf st fr target next next_fr value E Hs (Forall_inv Hframes)) as [Hs' Hfr'];
      split; [exact Hs'|split; [constructor; [exact Hfr'|exact (Forall_inv_tail Hframes)]|exact Hdead]].
  - destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:E.
    destruct (@side_free_get st fr target next next_fr value E Hs (Forall_inv Hframes)) as [Hs' Hfr'];
      split; [exact Hs'|split; [constructor; [exact Hfr'|exact (Forall_inv_tail Hframes)]|exact Hdead]].
Qed.
Lemma side_free_observed_get dirty tf st fr target tail k :
  side_free_config (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  side_free_config (observed_get dirty tf st fr target tail k).
Proof.
  intros [Hs [Hframes Hdead]]; unfold observed_get; destruct (R.is_materialized st target).
  - apply side_free_cursor; split; [exact Hs|split; [exact Hframes|exact Hdead]].
  - destruct (R.rank_lt st (R.frame_owner fr) target); [split; [exact Hs|split; [exact Hframes|exact Hdead]]|apply side_free_cursor; split; [exact Hs|split; [exact Hframes|exact Hdead]]].
Qed.
Lemma side_free_observed_spawn st fr target tail k :
  side_free_config (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  side_free_config (observed_spawn st fr target tail k).
Proof.
  intros [Hs [Hframes Hdead]]; unfold observed_spawn; destruct (R.is_materialized st target); [split; [exact Hs|split; [exact Hframes|exact Hdead]]|].
  destruct (R.rank_lt st (R.frame_owner fr) target); [split; [exact Hs|split; [exact Hframes|exact Hdead]]|].
  split; [now apply side_free_materialize|split; [exact Hframes|exact Hdead]].
Qed.
Lemma rhs_side_free tf roots st fr body k after : no_side_effects tf ->
  invariant tf roots (configuration st (R.RunRhs fr body k)) ->
  R.next_config tf (configuration st (R.RunRhs fr body k)) = Some after ->
  side_free_config (configuration st (R.RunRhs fr body k)) -> side_free_config after.
Proof.
  intros Hpure Hinv E [Hs [Hframes Hdead]]; change (Forall side_free_frame (fr :: suspended_frames k)) in Hframes.
  destruct (@ordinary_evaluation_sides tf _ fr body Hpure (proj1 (inv_control Hinv))) as [_ Hnoside].
  destruct body as [direct|target tail|target raw tail|target tail];
    unfold R.next_config,configuration in E; cbn [R.cfg_state R.cfg_control] in E.
  - inversion E; subst; split; [exact Hs|split; [exact Hframes|]].
    cbn [dead_empty]; split; [|exact Hdead]; destruct Features.eliminate_dead_sides; [apply set_empty_elements; exact (proj2 (Forall_inv Hframes))|reflexivity].
  - destruct (R.is_dormant st target).
    + inversion E; subst; split; [exact Hs|split; [exact Hframes|exact Hdead]].
    + assert (Hobserved : side_free_config (configuration (R.observe st target) (R.RunRhs fr (Syntax.Get target tail) k))).
      { split; [now apply side_free_observe|split; [exact Hframes|exact Hdead]]. }
      destruct (Ranks.lookup (R.ranking st) target).
      * rewrite ?option_cursor in E.
        assert (Eget : Some (observed_get true tf (R.observe st target) fr target tail k) = Some after).
        { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target);
            [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
        inversion Eget; subst; now apply side_free_observed_get.
      * destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)).
        -- inversion E; subst; split; [exact Hs|split; [exact Hframes|exact Hdead]].
        -- assert (Eget : Some (observed_get false tf (R.observe st target) fr target tail k) = Some after).
           { unfold observed_get,get_cursor; destruct (R.is_materialized (R.observe st target) target); cbn in E; rewrite ?option_cursor in E;
               [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
           inversion Eget; subst; now apply side_free_observed_get.
  - exfalso; exact (Hnoside target raw tail eq_refl).
  - destruct Features.defer_spawns.
    + inversion E; subst; split; [now apply side_free_request|split; [exact Hframes|exact Hdead]].
    + destruct (R.is_dormant st target); [inversion E; subst; split; [exact Hs|split; [exact Hframes|exact Hdead]]|].
      assert (Hobserved : side_free_config (configuration (R.observe st target) (R.RunRhs fr (Syntax.Spawn target tail) k))).
      { split; [now apply side_free_observe|split; [exact Hframes|exact Hdead]]. }
      destruct (Ranks.lookup (R.ranking st) target).
      * assert (Espawn : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
        { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
            [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
        inversion Espawn; subst; now apply side_free_observed_spawn.
      * destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)).
        -- inversion E; subst; split; [exact Hs|split; [exact Hframes|exact Hdead]].
        -- assert (Espawn : Some (observed_spawn (R.observe st target) fr target tail k) = Some after).
           { unfold observed_spawn; destruct (R.is_materialized (R.observe st target) target);
               [exact E|destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target); exact E]. }
           inversion Espawn; subst; now apply side_free_observed_spawn.
Qed.

Lemma side_free_step tf roots before after : no_side_effects tf -> invariant tf roots before ->
  R.next_config tf before = Some after -> side_free_config before -> side_free_config after.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hpure Hinv E Hfree.
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    destruct (R.queue st); cbn [R.queue_pop] in E.
    + destruct (R.pending_spawns st); [discriminate|]; inversion E; subst; exact Hfree.
    + inversion E; subst; exact Hfree.
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; destruct seeds as [|owner tail].
    + inversion E; subst; exact Hfree.
    + destruct (R.is_materialized st owner || R.is_dormant st owner); [inversion E; subst; exact Hfree|].
      destruct Hfree as [Hs [Hframes Hdead]]; destruct (Ranks.lookup (R.ranking st) owner).
      * inversion E; subst; split; [now apply side_free_observe|split; [exact Hframes|exact Hdead]].
      * destruct (R.pure_bottom_rhs tf owner); inversion E; subst;
          [split; [exact Hs|split; [exact Hframes|exact Hdead]]|split; [now apply side_free_observe|split; [exact Hframes|exact Hdead]]].
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    destruct (R.queue st); cbn [R.queue_pop] in E; inversion E; subst; exact Hfree.
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; inversion E; subst.
    destruct Hfree as [Hs [Hframes Hdead]].
    pose proof (@side_free_clear (R.materialize st owner) owner (@side_free_materialize st owner Hs)) as Hnext.
    split; [exact Hnext|split; [constructor; [now apply side_free_fresh|exact Hframes]|exact Hdead]].
  - exact (@rhs_side_free tf roots st fr body k after Hpure Hinv E Hfree).
  - destruct Hfree as [Hs [Hframes Hdead]]; change (pending = [] /\ dead_free_stack k) in Hdead; destruct Hdead as [-> Hdead].
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; inversion E; subst.
    split; [apply side_free_publish; [exact Hs|exact (Forall_inv Hframes)]|split; [exact Hframes|exact Hdead]].
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    destruct Hfree as [Hs [Hframes Hdead]]; change (Forall side_free_frame (fr :: suspended_frames k)) in Hframes.
    destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:Hwrite; inversion E; subst.
    destruct (@side_free_commit (R.flush_deferred st) fr direct next next_fr Hwrite Hs (Forall_inv Hframes)) as [Hs' Hfr'];
      split; [exact Hs'|split; [constructor; [exact Hfr'|exact (Forall_inv_tail Hframes)]|exact Hdead]].
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    destruct Hfree as [Hs [Hframes Hdead]]; change (Forall side_free_frame (fr :: suspended_frames k)) in Hframes.
    destruct (R.queue st) as [|head tail]; cbn [R.queue_peek R.queue_pop] in E.
    + inversion E; subst; split; [now apply side_free_reset|split; [exact (Forall_inv_tail Hframes)|exact Hdead]].
    + destruct (V.eq_dec head (R.frame_owner fr)) as [->|Hneq].
      * inversion E; subst; pose proof (@side_free_clear (R.with_queue st tail) (R.frame_owner fr) Hs) as Hnext;
          split; [exact Hnext|split; [constructor; [now apply side_free_fresh|exact (Forall_inv_tail Hframes)]|exact Hdead]].
      * destruct (R.rank_lt st (R.frame_owner fr) head); inversion E; subst.
        -- split; [exact Hs|split; [exact Hframes|exact Hdead]].
        -- split; [now apply side_free_reset|split; [exact (Forall_inv_tail Hframes)|exact Hdead]].
  - destruct k as [|seeds|fr target tail k|fr tail k|fr tail k|fr direct pending k|fr k];
      unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    + inversion E; subst; exact Hfree.
    + inversion E; subst; exact Hfree.
    + destruct Hfree as [Hs [Hframes Hdead]]; change (Forall side_free_frame (fr :: suspended_frames k)) in Hframes.
      destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:Hget; inversion E; subst.
      destruct (@side_free_get st fr target next next_fr value Hget Hs (Forall_inv Hframes)) as [Hs' Hfr'];
        split; [exact Hs'|split; [constructor; [exact Hfr'|exact (Forall_inv_tail Hframes)]|exact Hdead]].
    + inversion E; subst; exact Hfree.
    + inversion E; subst; exact Hfree.
    + destruct Hfree as [_ [_ Hdead]]; contradiction.
    + inversion E; subst; exact Hfree.
Qed.

Lemma initial_side_free roots : side_free_config (R.initial_config roots).
Proof.
  split; [|split; [constructor|exact I]].
  split; [reflexivity|split].
  - intro x; unfold R.is_side_dirty; cbn [R.initial_config R.cfg_state R.empty_state R.dirty_side_targets]; now rewrite ML.lookup_empty.
  - intros owner x; unfold R.lookup_set; cbn [R.initial_config R.cfg_state R.empty_state R.last_targets]; rewrite ML.lookup_empty; apply SL.empty_spec.
Qed.
Theorem ordinary_side_free tf roots c : no_side_effects tf -> Sem.steps tf (R.initial_config roots) c -> side_free_config c.
Proof.
  intros Hpure Hpath.
  assert (Hwalk : forall first last, Sem.steps tf first last -> Sem.steps tf (R.initial_config roots) first ->
    side_free_config first -> side_free_config last).
  { intros first last H; induction H; intros Hreach Hfree; [exact Hfree|].
    apply IHsteps; [eapply path_extend; eassumption|].
    exact (@side_free_step tf roots a b Hpure (proj2 (@reachable_invariants tf roots a Hreach)) H Hfree). }
  apply (Hwalk _ _ Hpath (@Sem.StepsRefl tf _) (initial_side_free roots)).
Qed.
Corollary ordinary_aggregate_bottom tf roots c target : no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) c -> R.aggregate (R.cfg_state c) target = D.bottom.
Proof.
  intros Hpure Hreach; pose proof (proj1 (proj1 (@ordinary_side_free tf roots c Hpure Hreach))) as Hempty.
  unfold R.aggregate,R.lookup_map; rewrite Hempty,ML.lookup_empty,ML.values_empty; reflexivity.
Qed.
Corollary ordinary_dirty_read_disabled tf roots c owner target : no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) c -> R.try_dirty_read tf (R.cfg_state c) owner target = None.
Proof.
  intros Hpure Hreach; pose proof (proj1 (proj2 (proj1 (@ordinary_side_free tf roots c Hpure Hreach)))) as Hdirty.
  unfold R.try_dirty_read; destruct (V.eq_dec owner target); [reflexivity|now rewrite Hdirty].
Qed.

Definition materialized_extension before after := forall x, R.is_materialized before x = true -> R.is_materialized after x = true.
Lemma materialized_same before after : R.sigma after = R.sigma before -> materialized_extension before after.
Proof. intros E x H; unfold R.is_materialized; rewrite E; exact H. Qed.
Lemma materialized_write st owner value : materialized_extension st (R.with_sigma st (M.update (R.sigma st) owner value)).
Proof.
  intros x H; unfold R.is_materialized; cbn [R.with_sigma R.sigma]; destruct (V.eq_dec x owner) as [->|Hneq].
  - now rewrite ML.lookup_update_same.
  - rewrite ML.lookup_update_other by exact Hneq; exact H.
Qed.
Lemma materialized_materialize st target : materialized_extension st (R.materialize st target).
Proof. unfold R.materialize; destruct (M.lookup _ _); [apply materialized_same; reflexivity|apply materialized_write]. Qed.
Lemma materialize_live st target : R.is_materialized (R.materialize st target) target = true.
Proof. unfold R.materialize; destruct (M.lookup (R.sigma st) target) eqn:E; unfold R.is_materialized; [now rewrite E|cbn; now rewrite ML.lookup_update_same]. Qed.
Lemma materialized_trans before middle after : materialized_extension before middle -> materialized_extension middle after -> materialized_extension before after.
Proof. intros H H' x Hx; exact (H' x (H x Hx)). Qed.
Lemma materialized_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  materialized_extension st next /\ R.is_materialized next target = true.
Proof.
  unfold R.complete_get; intro E; inversion E; subst; split.
  - eapply materialized_trans; [|apply materialized_materialize]; apply materialized_same; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
  - apply materialize_live.
Qed.
Lemma materialized_dirty_finish st target value : materialized_extension st (dirty_finish st target value).
Proof.
  intros x H; destruct value; [|exact H].
  unfold R.is_materialized,dirty_finish; cbn; destruct (V.eq_dec x target) as [->|Hneq];
    [now rewrite ML.lookup_update_same|rewrite ML.lookup_update_other by exact Hneq; exact H].
Qed.
Lemma materialized_dirty_get tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) -> materialized_extension st next.
Proof.
  unfold R.dirty_complete_get; intro E; inversion E; subst.
  set (prepared := R.materialize (if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) target).
  assert (Hprepared : materialized_extension st prepared).
  { unfold prepared; eapply materialized_trans; [|apply materialized_materialize]; apply materialized_same; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity. }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:Hdirty.
  - destruct (@dirty_read_result tf prepared (R.frame_owner fr) target s Hdirty) as [direct [v [_ [_ [-> _]]]]].
    eapply materialized_trans; [exact Hprepared|apply materialized_dirty_finish].
  - exact Hprepared.
Qed.
Lemma materialized_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) -> materialized_extension st next.
Proof.
  intro E; apply set_value_cases in E as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]];
    [apply materialized_same; reflexivity|apply materialized_same; reflexivity|].
  intros x H; unfold R.is_materialized,commit_publication; cbn;
    destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq];
    [now rewrite ML.lookup_update_same|rewrite ML.lookup_update_other by exact Hneq; exact H].
Qed.
Lemma side_write_sigma st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) -> R.sigma next = R.sigma st.
Proof.
  unfold R.write_side_contribution; intro E; inversion E; subst; unfold R.register_reset,R.promote_side_target;
    destruct (R.rank_lt _ _ _); reflexivity.
Qed.
Lemma materialized_observe st target : materialized_extension st (R.observe st target).
Proof. apply materialized_same; unfold R.observe; destruct (Ranks.observe _ _); reflexivity. Qed.
Lemma materialized_request st target : materialized_extension st (R.request_spawn st target).
Proof. apply materialized_same; unfold R.request_spawn; destruct (S.mem _ _); reflexivity. Qed.
Lemma materialized_reset st target : materialized_extension st (R.reset_registered_cells st target).
Proof. apply materialized_same; unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity. Qed.
Ltac materialized_after_step :=
  cbn [R.cfg_state R.cfg_control] in *;
  repeat first
    [ progress unfold R.materialize
    | match goal with |- context [match M.lookup _ _ with _ => _ end] => destruct (M.lookup _ _) eqn:? end
    | match goal with |- context [if ?test then _ else _] => destruct test eqn:? end ];
  first [apply materialized_same; reflexivity | apply materialized_write |
    apply materialized_same; unfold R.observe; destruct (Ranks.observe _ _); reflexivity |
    match goal with |- materialized_extension ?before (R.with_sigma ?base (M.update (R.sigma ?base) ?x ?value)) =>
      eapply (@materialized_trans before base _); [materialized_after_step|apply materialized_write] end |
    apply materialized_reset | apply materialized_request | apply materialized_observe |
    match goal with E : R.sigma ?after = R.sigma ?before |- materialized_extension ?before ?after => exact (materialized_same E) end |
    match goal with E : R.complete_get ?st ?fr ?target = _ |- _ =>
      let H := fresh in pose proof (proj1 (@materialized_get st fr target _ _ _ E)) as H;
      eapply materialized_trans; [|exact H]; materialized_after_step end |
    match goal with E : R.dirty_complete_get ?tf ?st ?fr ?target = _ |- _ =>
      let H := fresh in pose proof (@materialized_dirty_get tf st fr target _ _ _ E) as H;
      eapply materialized_trans; [|exact H]; materialized_after_step end |
    match goal with E : R.set_value ?st ?fr ?direct = _ |- _ =>
      let H := fresh in pose proof (@materialized_commit st fr direct _ _ E) as H;
      eapply materialized_trans; [|exact H]; materialized_after_step end |
    match goal with E : R.write_side_contribution ?st ?fr ?target ?input = _ |- _ =>
      let H := fresh in pose proof (@side_write_sigma st fr target input _ _ E) as H;
      match goal with |- materialized_extension ?before ?after =>
        eapply (@materialized_trans before st after);
        [materialized_after_step|apply materialized_same; cbn [R.enqueue R.mark_side_dirty R.with_queue R.with_dirty_side_targets R.sigma]; exact H] end end ].
Lemma next_materialized_extension tf before after : R.next_config tf before = Some after ->
  materialized_extension (R.cfg_state before) (R.cfg_state after).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    unfold R.next_config; cbn [R.cfg_state R.cfg_control]; intro E.
  - inspect_machine_step E; try discriminate; inversion E; subst; materialized_after_step.
  - destruct seeds; inspect_machine_step E; try discriminate; inversion E; subst; materialized_after_step.
  - inspect_machine_step E; try discriminate; inversion E; subst; materialized_after_step.
  - inversion E; subst; cbn; change (materialized_extension st (R.materialize st owner)); apply materialized_materialize.
  - destruct body; inspect_machine_step E; try discriminate; inversion E; subst; materialized_after_step.
  - destruct pending; inspect_machine_step E; try discriminate; inversion E; subst; materialized_after_step.
  - inspect_machine_step E; try discriminate; inversion E; subst; materialized_after_step.
  - inspect_machine_step E; try discriminate; inversion E; subst; materialized_after_step.
  - destruct k; inspect_machine_step E; try discriminate; inversion E; subst; materialized_after_step.
Qed.
Lemma path_materialized_extension tf before after : Sem.steps tf before after ->
  materialized_extension (R.cfg_state before) (R.cfg_state after).
Proof.
  intro H; induction H; [apply materialized_same; reflexivity|].
  exact (@materialized_trans _ _ _ (@next_materialized_extension tf a b H) IHsteps).
Qed.
Definition unmaterialized_credit support st := sum_nat support (fun x => if R.is_materialized st x then 0 else 1).
Lemma unmaterialized_credit_nonincreasing support before after : materialized_extension before after ->
  unmaterialized_credit support after <= unmaterialized_credit support before.
Proof.
  intro H; apply sum_nat_pointwise; intros x _; destruct (R.is_materialized before x) eqn:E;
    [rewrite (H x E)|destruct (R.is_materialized after x)]; lia.
Qed.
Lemma unmaterialized_credit_decreases support before after target : materialized_extension before after -> In target support ->
  R.is_materialized before target = false -> R.is_materialized after target = true ->
  unmaterialized_credit support after < unmaterialized_credit support before.
Proof.
  intros H Hin Hbefore Hafter; apply (@sum_nat_strict V.t support _ _ target); [|exact Hin|rewrite Hbefore,Hafter; lia].
  intros x _; destruct (R.is_materialized before x) eqn:E; [rewrite (H x E)|destruct (R.is_materialized after x)]; lia.
Qed.
Lemma unmaterialized_credit_equal support before after : materialized_extension before after ->
  unmaterialized_credit support after = unmaterialized_credit support before -> forall x, In x support ->
  R.is_materialized after x = R.is_materialized before x.
Proof.
  intros H E x Hin; destruct (R.is_materialized before x) eqn:Hbefore; [now rewrite (H x Hbefore)|].
  destruct (R.is_materialized after x) eqn:Hafter; [|reflexivity].
  pose proof (@unmaterialized_credit_decreases support before after x H Hin Hbefore Hafter); lia.
Qed.

Definition discovery_credit support st := sum_nat support (fun x => match Ranks.lookup (R.ranking st) x with Some _ => 0|None => 1 end).
Lemma discovery_credit_nonincreasing support before after : rank_extension before after ->
  discovery_credit support after <= discovery_credit support before.
Proof.
  intro H; apply sum_nat_pointwise; intros x _; destruct (Ranks.lookup (R.ranking before) x) eqn:E;
    [rewrite (H x n E)|destruct (Ranks.lookup (R.ranking after) x)]; lia.
Qed.
Lemma discovery_credit_decreases support before after target : rank_extension before after -> In target support ->
  Ranks.lookup (R.ranking before) target = None -> ranked after target ->
  discovery_credit support after < discovery_credit support before.
Proof.
  intros H Hin Hbefore [n Hafter]; apply (@sum_nat_strict V.t support _ _ target); [|exact Hin|rewrite Hbefore,Hafter; lia].
  intros x _; destruct (Ranks.lookup (R.ranking before) x) eqn:E;
    [rewrite (H x n0 E)|destruct (Ranks.lookup (R.ranking after) x)]; lia.
Qed.
Lemma discovery_credit_equal support before after : rank_extension before after ->
  discovery_credit support after = discovery_credit support before -> forall x, In x support ->
  Ranks.lookup (R.ranking after) x = Ranks.lookup (R.ranking before) x.
Proof.
  intros H E x Hin; destruct (Ranks.lookup (R.ranking before) x) eqn:Hbefore; [exact (H x n Hbefore)|].
  destruct (Ranks.lookup (R.ranking after) x) eqn:Hafter; [|reflexivity].
  pose proof (@discovery_credit_decreases support before after x H Hin Hbefore ltac:(exists n; exact Hafter)); lia.
Qed.
Corollary equal_discovery_order support before after x y : rank_extension before after ->
  discovery_credit support after = discovery_credit support before -> In x support -> In y support ->
  R.rank_lt after x y = R.rank_lt before x y.
Proof.
  intros H E Hx Hy; unfold R.rank_lt,R.ranking_lt.
  now rewrite (@discovery_credit_equal support before after H E x Hx),(@discovery_credit_equal support before after H E y Hy).
Qed.
Lemma fresh_discovery_higher st owner target : ranked st owner -> Ranks.lookup (R.ranking st) target = None ->
  R.rank_lt (R.observe st target) owner target = true.
Proof.
  intros [n Howner] Htarget; unfold R.observe; destruct (Ranks.observe (R.ranking st) target) as [order rank] eqn:E.
  pose proof (@RankLaws.observe_lookup (R.ranking st) target order rank E) as Hnew;
    pose proof (@RankLaws.observe_preserves (R.ranking st) target order rank owner n E Howner) as Hold.
  change (Ranks.lookup order target = Some rank) in Hnew; change (Ranks.lookup order owner = Some n) in Hold.
  unfold R.rank_lt,R.ranking_lt; cbn [R.with_ranking R.ranking]; rewrite Hold,Hnew.
  exact (@RankLaws.observe_fresh_above (R.ranking st) target order rank owner n Htarget E Howner).
Qed.
Definition activation_credit support st := discovery_credit support st + unmaterialized_credit support st.
Theorem activation_credit_path support tf before after : Sem.steps tf before after ->
  activation_credit support (R.cfg_state after) <= activation_credit support (R.cfg_state before).
Proof.
  intro H; unfold activation_credit.
  pose proof (@discovery_credit_nonincreasing support _ _ (@path_rank_extension tf before after H));
    pose proof (@unmaterialized_credit_nonincreasing support _ _ (@path_materialized_extension tf before after H)); lia.
Qed.
Theorem activation_credit_equal support tf before after : Sem.steps tf before after ->
  activation_credit support (R.cfg_state after) = activation_credit support (R.cfg_state before) -> forall x, In x support ->
  Ranks.lookup (R.ranking (R.cfg_state after)) x = Ranks.lookup (R.ranking (R.cfg_state before)) x /\
  R.is_materialized (R.cfg_state after) x = R.is_materialized (R.cfg_state before) x.
Proof.
  intros H E x Hin; pose proof (@path_rank_extension tf before after H) as Hr;
    pose proof (@path_materialized_extension tf before after H) as Hm.
  pose proof (@discovery_credit_nonincreasing support _ _ Hr) as Hdiscovery;
    pose proof (@unmaterialized_credit_nonincreasing support _ _ Hm) as Hmaterialized.
  unfold activation_credit in E; split;
    [apply (@discovery_credit_equal support _ _ Hr)|apply (@unmaterialized_credit_equal support _ _ Hm)]; [lia|exact Hin|lia|exact Hin].
Qed.

(** An uncontrolled value only invalidates lower readers. Unknown dormant
    targets are allowed until observation assigns their fresh, higher rank. *)
Definition reader_orientation st := forall target reader,
  S.mem reader (R.lookup_set (R.readers st) target) = true ->
  S.mem target (R.controlled st) = true \/ Ranks.lookup (R.ranking st) target = None \/ R.rank_lt st reader target = true.
Lemma orientation_fields before after : R.readers after = R.readers before ->
  R.ranking after = R.ranking before -> R.controlled after = R.controlled before ->
  reader_orientation before -> reader_orientation after.
Proof. intros Hread Hrank Hcontrolled; unfold reader_orientation,R.rank_lt; now rewrite Hread,Hrank,Hcontrolled. Qed.
Lemma orientation_promote st target : reader_orientation st -> reader_orientation (R.promote_controlled st target).
Proof.
  intros H key reader Hin; destruct (H key reader Hin) as [Hc|[Hnone|Hlt]];
    [left; apply SL.add_spec; now right|right; now left|right; now right].
Qed.
Lemma orientation_materialize st target : reader_orientation st -> reader_orientation (R.materialize st target).
Proof. unfold R.materialize; destruct (M.lookup _ _); exact (fun H => H). Qed.
Lemma observe_readers_table st target : R.readers (R.observe st target) = R.readers st.
Proof. unfold R.observe; destruct (Ranks.observe _ _); reflexivity. Qed.
Lemma orientation_observe st target :
  (forall key reader, S.mem reader (R.lookup_set (R.readers st) key) = true -> ranked st reader) ->
  reader_orientation st -> reader_orientation (R.observe st target).
Proof.
  intros Hread H key reader Hin; rewrite observe_readers_table in Hin; destruct (H key reader Hin) as [Hc|[Hnone|Hlt]].
  - left; unfold R.observe; destruct (Ranks.observe _ _); exact Hc.
  - destruct (V.eq_dec key target) as [->|Hneq].
    + right; right; exact (@fresh_discovery_higher st reader target (Hread target reader Hin) Hnone).
    + right; left; unfold R.observe; destruct (Ranks.observe (R.ranking st) target) as [order rank] eqn:E;
        cbn [R.with_ranking R.ranking].
      destruct (Ranks.lookup (R.ranking st) target) as [n|] eqn:Ht.
      * pose proof (@RankLaws.observe_existing (R.ranking st) target n Ht) as Hsame;
          change (Ranks.observe (R.ranking st) target = (R.ranking st,n)) in Hsame; rewrite E in Hsame; inversion Hsame; subst; exact Hnone.
      * exact (@RankLaws.observe_fresh_preserves_absent (R.ranking st) target order rank key Ht E Hneq Hnone).
  - right; right; exact (@rank_lt_extension st (R.observe st target) reader key (observe_extends st target) Hlt).
Qed.
Lemma orientation_dormant_read st owner target : Ranks.lookup (R.ranking st) target = None ->
  reader_orientation st -> reader_orientation (R.add_reader st target owner).
Proof.
  intros Hnone H key reader Hin; unfold R.add_reader,R.lookup_set in Hin; cbn [R.with_readers R.readers] in Hin.
  destruct (V.eq_dec key target) as [->|Hneq].
  - right; left; exact Hnone.
  - rewrite ML.lookup_update_other in Hin by exact Hneq; exact (H key reader Hin).
Qed.
Lemma orientation_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  reader_orientation st -> reader_orientation next.
Proof.
  unfold R.complete_get; intro E; inversion E; subst; intro H; apply orientation_materialize.
  intros key reader Hin; unfold R.lookup_set in Hin; cbn [R.with_readers R.readers] in Hin.
  destruct (V.eq_dec key target) as [->|Hneq].
  - rewrite ML.lookup_update_same in Hin; apply SL.add_spec in Hin as [->|Hin].
    + destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hlt;
        [right; right; exact Hlt|left; apply SL.add_spec; now left].
    + destruct (R.rank_lt st (R.frame_owner fr) target);
        [exact (H target reader Hin)|exact (@orientation_promote st target H target reader Hin)].
  - rewrite ML.lookup_update_other in Hin by exact Hneq.
    destruct (R.rank_lt st (R.frame_owner fr) target);
      [exact (H key reader Hin)|exact (@orientation_promote st target H key reader Hin)].
Qed.
Lemma is_dormant_unranked st target : R.is_dormant st target = true -> Ranks.lookup (R.ranking st) target = None.
Proof.
  unfold R.is_dormant; intro H; apply andb_true_iff in H as [_ H]; apply andb_true_iff in H as [_ H].
  destruct (Ranks.lookup _ _) eqn:E; [discriminate|reflexivity].
Qed.
Lemma orientation_dirty_finish st target value : reader_orientation st -> reader_orientation (dirty_finish st target value).
Proof.
  intros H key reader Hin; pose proof (@dirty_finish_reader_subset st target value key reader Hin) as Hold.
  destruct (@orientation_promote st target H key reader Hold) as [Hc|[Hnone|Hlt]];
    [left; destruct value; exact Hc|right; left; destruct value; exact Hnone|right; right; destruct value; exact Hlt].
Qed.
Lemma orientation_dirty_get tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  reader_orientation st -> reader_orientation next.
Proof.
  unfold R.dirty_complete_get; intro E; inversion E; subst; intro H.
  set (prepared := R.materialize (if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) target).
  assert (Hprepared : reader_orientation prepared).
  { unfold prepared; apply orientation_materialize; destruct (R.rank_lt st (R.frame_owner fr) target); auto using orientation_promote. }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:Hdirty.
  - destruct (@dirty_read_result tf prepared (R.frame_owner fr) target s Hdirty) as [direct [v [_ [_ [-> _]]]]].
    intros key reader Hin; destruct (V.eq_dec key target) as [->|Hneq].
    + left; destruct v; apply SL.add_spec; now left.
    + unfold R.add_reader,R.lookup_set in Hin; cbn [R.with_readers R.readers] in Hin.
      rewrite ML.lookup_update_other in Hin by exact Hneq; exact (@orientation_dirty_finish prepared target v Hprepared key reader Hin).
  - intros key reader Hin; unfold R.add_reader,R.lookup_set in Hin; cbn [R.with_readers R.readers] in Hin.
    destruct (V.eq_dec key target) as [->|Hneq].
    + rewrite ML.lookup_update_same in Hin; apply SL.add_spec in Hin as [->|Hin].
      * unfold prepared; destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hlt.
        -- right; right; change (R.rank_lt (R.materialize st target) (R.frame_owner fr) target = true).
           unfold R.rank_lt; rewrite materialize_ranking; exact Hlt.
        -- left; unfold R.materialize; destruct (M.lookup _ _); apply SL.add_spec; now left.
      * exact (Hprepared target reader Hin).
    + rewrite ML.lookup_update_other in Hin by exact Hneq; exact (Hprepared key reader Hin).
Qed.
Lemma orientation_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  reader_orientation st -> reader_orientation next.
Proof.
  intros E H key reader Hin.
  pose proof (@set_value_readers_subset st fr direct next next_fr E key reader Hin) as Hold.
  destruct (H key reader Hold) as [Hc|[Hnone|Hlt]].
  all: apply set_value_cases in E as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; auto.
Qed.
Lemma uncontrolled_publication_lower st owner value target : reader_orientation st -> ranked st owner ->
  S.mem owner (R.controlled st) = false -> In target (R.queue (commit_publication st owner value)) ->
  ~ In target (R.queue st) -> R.rank_lt st target owner = true.
Proof.
  intros Horientation Howner Hcontrolled Hin Hnew; apply publication_members in Hin as [Hin|[Hin|[_ [Hc _]]]]; [contradiction| |congruence].
  destruct (Horientation owner target Hin) as [Hc|[Hnone|Hlt]]; [congruence|destruct Howner as [n Hn]; congruence|exact Hlt].
Qed.

Lemma orientation_side_write st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) ->
  reader_orientation st -> reader_orientation next.
Proof.
  unfold R.write_side_contribution; intro E; inversion E; subst; intro H.
  change (reader_orientation (R.promote_side_target st fr target)).
  unfold R.promote_side_target; destruct (R.rank_lt _ _ _); auto using orientation_promote.
Qed.
Lemma orientation_request st target : reader_orientation st -> reader_orientation (R.request_spawn st target).
Proof. unfold R.request_spawn; destruct (S.mem _ _); exact (fun H => H). Qed.
Lemma orientation_reset st target : reader_orientation st -> reader_orientation (R.reset_registered_cells st target).
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; exact (fun H => H). Qed.
Lemma orientation_enqueue st target : reader_orientation st -> reader_orientation (R.enqueue st target).
Proof. exact (fun H => H). Qed.
Lemma orientation_mark_dirty st target : reader_orientation st -> reader_orientation (R.mark_side_dirty st target).
Proof. exact (fun H => H). Qed.
Ltac orientation_after_step Horientation Hreaders :=
  cbn [R.cfg_state R.cfg_control] in *;
  first
    [ exact Horientation
    | apply orientation_enqueue; orientation_after_step Horientation Hreaders
    | apply orientation_mark_dirty; orientation_after_step Horientation Hreaders
    | match goal with |- context [if ?test then _ else _] => destruct test eqn:?; orientation_after_step Horientation Hreaders end
    | apply orientation_materialize; orientation_after_step Horientation Hreaders
    | apply orientation_observe; [exact Hreaders|exact Horientation]
    | apply orientation_request; exact Horientation
    | apply orientation_reset; exact Horientation
    | apply orientation_dormant_read; [assumption|exact Horientation]
    | apply orientation_dormant_read; [eapply is_dormant_unranked; eassumption|exact Horientation]
    | match goal with E : R.complete_get ?base ?fr ?target = _ |- _ =>
        eapply orientation_get; [exact E|orientation_after_step Horientation Hreaders] end
    | match goal with E : R.dirty_complete_get ?tf ?base ?fr ?target = _ |- _ =>
        eapply orientation_dirty_get; [exact E|orientation_after_step Horientation Hreaders] end
    | match goal with E : R.set_value ?base ?fr ?direct = _ |- _ =>
        eapply orientation_commit; [exact E|orientation_after_step Horientation Hreaders] end
    | match goal with E : R.write_side_contribution ?base ?fr ?target ?input = _ |- _ =>
        eapply orientation_side_write; [exact E|orientation_after_step Horientation Hreaders] end
    | unfold R.materialize; destruct (M.lookup _ _); orientation_after_step Horientation Hreaders ].
Theorem orientation_step tf roots before after : invariant tf roots before ->
  R.next_config tf before = Some after -> reader_orientation (R.cfg_state before) -> reader_orientation (R.cfg_state after).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hinv E Horientation; pose proof (shape_readers (inv_shape Hinv)) as Hreaders;
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - inspect_machine_step E; try discriminate; inversion E; subst; orientation_after_step Horientation Hreaders.
  - destruct seeds; inspect_machine_step E; try discriminate; inversion E; subst; orientation_after_step Horientation Hreaders.
  - inspect_machine_step E; try discriminate; inversion E; subst; orientation_after_step Horientation Hreaders.
  - inversion E; subst; orientation_after_step Horientation Hreaders.
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end; inspect_machine_step E; try discriminate; inversion E; subst; orientation_after_step Horientation Hreaders.
  - destruct pending; inspect_machine_step E; try discriminate; inversion E; subst; orientation_after_step Horientation Hreaders.
  - inspect_machine_step E; try discriminate; inversion E; subst; orientation_after_step Horientation Hreaders.
  - inspect_machine_step E; try discriminate; inversion E; subst; orientation_after_step Horientation Hreaders.
  - destruct k; inspect_machine_step E; try discriminate; inversion E; subst; orientation_after_step Horientation Hreaders.
Qed.
Lemma initial_orientation roots : reader_orientation (R.cfg_state (R.initial_config roots)).
Proof.
  intros target reader Hin; change (S.mem reader (R.lookup_set (M.empty S.t) target) = true) in Hin.
  unfold R.lookup_set in Hin; rewrite ML.lookup_empty,SL.empty_spec in Hin; discriminate.
Qed.
Theorem reachable_reader_orientation tf roots c : Sem.steps tf (R.initial_config roots) c -> reader_orientation (R.cfg_state c).
Proof.
  intro Hpath; assert (Hwalk : forall first last, Sem.steps tf first last -> Sem.steps tf (R.initial_config roots) first ->
    reader_orientation (R.cfg_state first) -> reader_orientation (R.cfg_state last)).
  { intros first last H; induction H; intros Hr Ho; [exact Ho|].
    apply IHsteps; [eapply path_extend; eassumption|].
    exact (@orientation_step tf roots a b (proj2 (@reachable_invariants tf roots a Hr)) H Ho). }
  exact (Hwalk _ _ Hpath (@Sem.StepsRefl tf _) (initial_orientation roots)).
Qed.

(** Deferred demands have their own finite credit. A first request moves one
    unit into the FIFO, and taking its head spends that unit. *)
Definition spawn_view before after := R.pending_spawns after = R.pending_spawns before /\
  R.requested_spawns after = R.requested_spawns before.
Lemma spawn_view_refl st : spawn_view st st.
Proof. split; reflexivity. Qed.
Lemma spawn_view_trans before middle after : spawn_view before middle -> spawn_view middle after -> spawn_view before after.
Proof. intros [Hp Hr] [Hp' Hr']; split; congruence. Qed.
Lemma get_spawn_view st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) -> spawn_view st next.
Proof.
  unfold R.complete_get,R.materialize; intro E; inversion E; subst; unfold spawn_view;
    destruct (M.lookup _ _); destruct (R.rank_lt _ _ _); split; reflexivity.
Qed.
Lemma dirty_spawn_view tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) -> spawn_view st next.
Proof.
  unfold R.dirty_complete_get; set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  set (prepared := R.materialize base target).
  assert (Hbase : spawn_view st prepared).
  { unfold spawn_view,prepared,R.materialize,base; destruct (M.lookup _ _); destruct (R.rank_lt _ _ _); split; reflexivity. }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:E; intro H; inversion H; subst.
  - destruct (@dirty_read_result tf prepared (R.frame_owner fr) target s E) as [direct [updated [_ [_ [-> _]]]]].
    destruct updated; exact Hbase.
  - exact Hbase.
Qed.
Ltac spawn_metadata :=
  repeat match goal with
  | E : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let H := fresh "Hspawn" in pose proof (@get_spawn_view base fr target next next_fr value E) as H; destruct H; clear E
  | E : R.dirty_complete_get ?tf ?base ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let H := fresh "Hspawn" in pose proof (@dirty_spawn_view tf base fr target next next_fr value E) as H; destruct H; clear E
  | E : R.set_value ?base ?fr ?direct = (?next,?next_fr) |- _ =>
      let H := fresh "Hspawn" in pose proof (@set_value_metadata base fr direct next next_fr E) as H;
      destruct H as [_ [_ [_ [_ [? ?]]]]]; clear E
  | E : R.write_side_contribution ?base ?fr ?target ?input = (?next,?changed) |- _ =>
      let H := fresh "Hspawn" in pose proof (@side_write_metadata base fr target input next changed E) as H;
      destruct H as [_ [_ [_ [_ [_ [_ [? ?]]]]]]]; clear E
  end.
Ltac spawn_view_case E :=
  inspect_machine_step E; try discriminate; inversion E; subst; spawn_metadata; left; unfold spawn_view;
  cbn [R.cfg_state R.enqueue R.with_queue R.with_spawns R.mark_side_dirty R.clear_side_dirty R.with_dirty_side_targets
    R.add_reader R.with_readers R.remember_dormant R.with_dormant_bottom R.publish_targets R.with_last_targets];
  repeat first
  [ match goal with H : R.pending_spawns ?a = R.pending_spawns ?b |- _ => progress rewrite H end
  | match goal with H : R.requested_spawns ?a = R.requested_spawns ?b |- _ => progress rewrite H end
  | progress unfold R.observe; destruct (Ranks.observe _ _)
  | progress unfold R.materialize; destruct (M.lookup _ _)
  | progress unfold R.reset_registered_cells; destruct Features.restart_side_phases
  | match goal with |- context [if ?test then _ else _] => destruct test eqn:? end
  | progress cbn [R.enqueue R.with_queue R.mark_side_dirty R.clear_side_dirty R.with_dirty_side_targets
      R.add_reader R.with_readers R.remember_dormant R.with_dormant_bottom R.publish_targets R.with_last_targets R.promote_controlled R.with_controlled] ];
  cbn; repeat match goal with H : R.pending_spawns ?a = R.pending_spawns ?b |- _ => progress rewrite H | H : R.requested_spawns ?a = R.requested_spawns ?b |- _ => progress rewrite H end;
  try (unfold R.observe; destruct (Ranks.observe _ _)); split; reflexivity || assumption.
Theorem spawn_step_shape tf before after : R.next_config tf before = Some after ->
  spawn_view (R.cfg_state before) (R.cfg_state after) \/
  (exists target, In target (exposed (R.cfg_control before)) /\ spawn_view (R.request_spawn (R.cfg_state before) target) (R.cfg_state after)) \/
  (exists target rest, R.pending_spawns (R.cfg_state before) = target :: rest /\
    R.pending_spawns (R.cfg_state after) = rest /\ R.requested_spawns (R.cfg_state after) = R.requested_spawns (R.cfg_state before)).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intro E; unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - destruct (R.queue st) as [|owner rest]; cbn [R.queue_pop] in E.
    + destruct (R.pending_spawns st) as [|target rest] eqn:Efifo; [discriminate|].
      inversion E; subst; right; right; exists target,rest; repeat split; assumption || reflexivity.
    + inversion E; subst; left; split; reflexivity.
  - destruct seeds; spawn_view_case E.
  - spawn_view_case E.
  - spawn_view_case E.
  - destruct body as [direct|target tail|target raw tail|target tail].
    + spawn_view_case E.
    + repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
        spawn_view_case E.
    + spawn_view_case E.
    + destruct Features.defer_spawns eqn:Edefer.
      * inversion E; subst; right; left; exists target; split; [now left|apply spawn_view_refl].
      * spawn_view_case E.
  - destruct pending; spawn_view_case E.
  - spawn_view_case E.
  - spawn_view_case E.
  - destruct k; spawn_view_case E.
Qed.
Definition fifo_registered st := NoDup (R.pending_spawns st) /\ forall target,
  In target (R.pending_spawns st) -> S.mem target (R.requested_spawns st) = true.
Lemma fifo_request st target : fifo_registered st -> fifo_registered (R.request_spawn st target).
Proof.
  intros [Hdistinct Hregistered]; unfold R.request_spawn; destruct (S.mem target (R.requested_spawns st)) eqn:E; [now split|].
  cbn; split.
  - apply NoDup_app; repeat split; [exact Hdistinct|repeat constructor; cbn; tauto|].
    intros x Hin Hlast; cbn in Hlast; destruct Hlast as [<-|Hbad]; [|contradiction].
    rewrite (Hregistered target Hin) in E; discriminate.
  - intros x Hin; apply in_app_iff in Hin as [Hin|[<-|Hbad]]; [apply SL.add_spec; right; exact (Hregistered x Hin)|apply SL.add_spec; now left|contradiction].
Qed.
Theorem reachable_fifo_registered tf roots c : Sem.steps tf (R.initial_config roots) c -> fifo_registered (R.cfg_state c).
Proof.
  assert (Hwalk : forall a b, Sem.steps tf a b -> fifo_registered (R.cfg_state a) -> fifo_registered (R.cfg_state b)).
  { intros a b H; induction H; intros Hfifo; [exact Hfifo|apply IHsteps].
    destruct (@spawn_step_shape tf a b H) as [[Hp Hr]|[[target [_ [Hp Hr]]]|[target [rest [Hbefore [Hp Hr]]]]]].
    - unfold fifo_registered in *; now rewrite Hp,Hr.
    - unfold fifo_registered; rewrite Hp,Hr; exact (fifo_request target Hfifo).
    - unfold fifo_registered in *; rewrite Hp,Hr; destruct Hfifo as [Hdistinct Hregistered]; split.
      + rewrite Hbefore in Hdistinct; now inversion Hdistinct.
      + intros x Hin; apply Hregistered; rewrite Hbefore; now right.
  }
  intro Hreach; apply (Hwalk _ _ Hreach); split; [constructor|intros target Hin; contradiction].
Qed.
Definition spawn_credit support st := sum_nat support (fun target => if S.mem target (R.requested_spawns st) then 0 else 1) + length (R.pending_spawns st).
Lemma spawn_credit_view support before after : spawn_view before after -> spawn_credit support after = spawn_credit support before.
Proof. intros [Hp Hr]; unfold spawn_credit; now rewrite Hp,Hr. Qed.
Lemma spawn_credit_request support st target : In target support -> spawn_credit support (R.request_spawn st target) <= spawn_credit support st.
Proof.
  intro Hin; unfold R.request_spawn; destruct (S.mem target (R.requested_spawns st)) eqn:E; [lia|].
  unfold spawn_credit; cbn [R.with_spawns R.requested_spawns R.pending_spawns]; rewrite length_app; cbn.
  assert (Hcredit : sum_nat support (fun x => if S.mem x (S.add target (R.requested_spawns st)) then 0 else 1) <
    sum_nat support (fun x => if S.mem x (R.requested_spawns st) then 0 else 1)).
  { apply (@sum_nat_strict V.t support _ _ target); [|exact Hin|].
    - intros x _; cbn; destruct (S.mem x (R.requested_spawns st)) eqn:Ex;
        [assert (S.mem x (S.add target (R.requested_spawns st)) = true) by (apply SL.add_spec; now right); rewrite H; lia|destruct (S.mem x (S.add target (R.requested_spawns st))); lia].
    - assert (S.mem target (S.add target (R.requested_spawns st)) = true) by (apply SL.add_spec; now left).
      cbn; rewrite H,E; lia. }
  lia.
Qed.
Theorem spawn_credit_step tf roots (finite : Sem.finite_system tf roots) before after :
  Sem.steps tf (R.initial_config roots) before -> R.next_config tf before = Some after ->
  spawn_credit (Sem.support finite) (R.cfg_state after) <= spawn_credit (Sem.support finite) (R.cfg_state before).
Proof.
  intros Hreach Hstep; destruct (@spawn_step_shape tf before after Hstep) as [Hview|[[target [Hin Hview]]|[target [rest [Hbefore [Hp Hr]]]]]].
  - rewrite (spawn_credit_view _ Hview); lia.
  - rewrite (spawn_credit_view _ Hview); apply spawn_credit_request.
    destruct (@reachable_support tf roots finite before Hreach) as [Hrank Hschedule].
    exact (proj1 (Forall_forall _ _) (@exposed_supported tf roots (Sem.support finite) before
      (Sem.system_supported finite) Hrank Hschedule (proj2 (@reachable_invariants tf roots before Hreach))) target Hin).
  - unfold spawn_credit; rewrite Hp,Hr,Hbefore; cbn; lia.
Qed.

Lemma spawn_credit_pop support st target rest : R.pending_spawns st = target :: rest ->
  spawn_credit support (R.with_spawns st rest (R.requested_spawns st)) < spawn_credit support st.
Proof. intro E; unfold spawn_credit; cbn; rewrite E; cbn; lia. Qed.
Lemma spawn_credit_initial support roots : spawn_credit support (R.cfg_state (R.initial_config roots)) = length support.
Proof.
  unfold spawn_credit,sum_nat; cbn [R.initial_config R.cfg_state R.empty_state R.pending_spawns R.requested_spawns].
  rewrite Nat.add_0_r; induction support; cbn; [reflexivity|now rewrite SL.empty_spec,IHsupport].
Qed.
Theorem spawn_credit_path tf roots (finite : Sem.finite_system tf roots) before after :
  Sem.steps tf (R.initial_config roots) before -> Sem.steps tf before after ->
  spawn_credit (Sem.support finite) (R.cfg_state after) <= spawn_credit (Sem.support finite) (R.cfg_state before).
Proof.
  intros Hreach Hpath; induction Hpath; [lia|].
  pose proof (@spawn_credit_step tf roots finite a b Hreach H) as Hstep.
  specialize (IHHpath (@path_extend tf _ a b Hreach H)); lia.
Qed.
Theorem reachable_spawn_credit_bound tf roots (finite : Sem.finite_system tf roots) c :
  Sem.steps tf (R.initial_config roots) c -> spawn_credit (Sem.support finite) (R.cfg_state c) <= length (Sem.support finite).
Proof.
  intro Hreach; pose proof (@spawn_credit_path tf roots finite _ c (@Sem.StepsRefl tf _) Hreach) as Hbound;
    now rewrite spawn_credit_initial in Hbound.
Qed.

(** With ordinary deferred spawning, a discovered owner is materialized
    before the machine reads another right-hand side. *)
Definition starting c owner := exists k, R.cfg_control c = R.StartEpisode owner k.
Definition activation_frontier c := forall owner, ranked (R.cfg_state c) owner ->
  R.is_materialized (R.cfg_state c) owner = true \/ starting c owner.
Definition fully_materialized st := forall owner, ranked st owner -> R.is_materialized st owner = true.
Lemma activation_not_start c : activation_frontier c -> (forall owner, ~ starting c owner) -> fully_materialized (R.cfg_state c).
Proof. intros H Hnone owner Hrank; destruct (H owner Hrank); [assumption|now exfalso; apply (Hnone owner)]. Qed.
Lemma observe_materialized st target owner : R.is_materialized (R.observe st target) owner = R.is_materialized st owner.
Proof. unfold R.observe; destruct (Ranks.observe _ _); reflexivity. Qed.
Lemma observe_existing_ranking st target n : Ranks.lookup (R.ranking st) target = Some n ->
  R.ranking (R.observe st target) = R.ranking st.
Proof.
  intro H; pose proof (@RankLaws.observe_existing (R.ranking st) target n H) as E;
    change (Ranks.observe (R.ranking st) target = (R.ranking st,n)) in E;
    unfold R.observe; now rewrite E.
Qed.
Lemma unexposed_ranking tf before after : exposed (R.cfg_control before) = [] -> R.next_config tf before = Some after ->
  R.ranking (R.cfg_state after) = R.ranking (R.cfg_state before).
Proof. intros Hempty E; destruct (@ranking_step_view tf before after E) as [Hsame|[target [Hin _]]]; [exact Hsame|rewrite Hempty in Hin; contradiction]. Qed.
Lemma activation_same_step tf before after : R.next_config tf before = Some after -> activation_frontier before ->
  (forall owner, ~ starting before owner) -> R.ranking (R.cfg_state after) = R.ranking (R.cfg_state before) -> activation_frontier after.
Proof.
  intros E Hfront Hnone Hr owner Hrank; left; apply (@next_materialized_extension tf before after E).
  apply (activation_not_start Hfront Hnone); unfold ranked in *; now rewrite Hr in Hrank.
Qed.
Lemma activation_observe_start st target k : fully_materialized st -> activation_frontier (configuration (R.observe st target) (R.StartEpisode target k)).
Proof.
  intros Hfull owner Hrank; cbn [configuration R.cfg_state] in Hrank |- *; apply observe_ranked_cases in Hrank as [Hrank|Heq].
  - left; rewrite observe_materialized; exact (Hfull owner Hrank).
  - subst owner; right; now exists k.
Qed.
Ltac activation_no_start := let target := fresh "owner_start" in let rest := fresh "rest_start" in let Hbad := fresh "Hstart_bad" in intros target [rest Hbad]; discriminate.
Ltac activation_unchanged E Hfront :=
  match type of E with R.next_config ?tf ?before = Some ?after =>
    eapply (@activation_same_step tf before after); [exact E|exact Hfront|activation_no_start|exact (@unexposed_ranking tf before after eq_refl E)] end.
Theorem activation_frontier_step tf roots before after : Features.defer_spawns = true -> no_side_effects tf ->
  invariant tf roots before -> activation_frontier before -> R.next_config tf before = Some after -> activation_frontier after.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hdefer Hpure Hinv Hfront E.
  - activation_unchanged E Hfront.
  - assert (Hfull : fully_materialized st) by (apply (activation_not_start Hfront); activation_no_start).
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; destruct seeds as [|root rest].
    + inversion E; subst; intros x Hrank; left; exact (Hfull x Hrank).
    + destruct (R.is_materialized st root || R.is_dormant st root).
      * inversion E; subst; intros x Hrank; left; exact (Hfull x Hrank).
      * destruct (Ranks.lookup (R.ranking st) root); [inversion E; subst; now apply activation_observe_start|].
        destruct (R.pure_bottom_rhs tf root).
        -- inversion E; subst; intros x Hrank; left; exact (Hfull x Hrank).
        -- inversion E; subst; now apply activation_observe_start.
  - activation_unchanged E Hfront.
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; inversion E; subst.
    intros x Hrank; change (ranked (R.clear_side_dirty (R.materialize st owner) owner) x) in Hrank;
      unfold ranked in Hrank; rewrite clear_ranking,materialize_ranking in Hrank.
    destruct (Hfront x Hrank) as [Hlive|[rest Hstart]].
    + left; change (R.is_materialized (R.materialize st owner) x = true); apply materialized_materialize; exact Hlive.
    + change (R.StartEpisode owner k = R.StartEpisode x rest) in Hstart; inversion Hstart; subst x; left; apply materialize_live.
  - assert (Hfull : fully_materialized st) by (apply (activation_not_start Hfront); activation_no_start).
    destruct body as [direct|target tail|target raw tail|target tail].
    + activation_unchanged E Hfront.
    + pose proof E as Estep; unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
      destruct (R.is_dormant st target).
      * inversion E; subst; intros x Hrank; left; exact (Hfull x Hrank).
      * destruct (Ranks.lookup (R.ranking st) target) as [rank|] eqn:Hknown.
        -- assert (Hlive : R.is_materialized (R.observe st target) target = true) by
            (rewrite observe_materialized; apply Hfull; now exists rank).
           rewrite Hlive in E; destruct (R.dirty_complete_get tf (R.observe st target) fr target) as [[next next_fr] value] eqn:Eg;
             inversion E; subst; intros x Hrank; left; apply (@materialized_dirty_get tf (R.observe st target) fr target next next_fr value Eg).
           rewrite observe_materialized; apply Hfull; unfold ranked in *; cbn [R.cfg_state] in Hrank; now rewrite (@dirty_get_ranking tf (R.observe st target) fr target next next_fr value Eg), (@observe_existing_ranking st target rank Hknown) in Hrank.
        -- destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)) eqn:Hbottom.
           ++ inversion E; subst; intros x Hrank; left; exact (Hfull x Hrank).
           ++ assert (Howner : ranked st (R.frame_owner fr)).
              { apply (proj1 (Forall_forall _ _) (shape_stack_ranks (inv_shape Hinv))); cbn; now left. }
              assert (Hunmaterialized : R.is_materialized (R.observe st target) target = false).
              { rewrite observe_materialized; destruct (R.is_materialized st target) eqn:Hx; [|reflexivity].
                destruct (shape_materialized (inv_shape Hinv) target Hx) as [n Hn]; change (Ranks.lookup (R.ranking st) target = Some n) in Hn; rewrite Hknown in Hn; discriminate. }
              rewrite Hunmaterialized,(@fresh_discovery_higher st (R.frame_owner fr) target Howner Hknown) in E; cbn in E;
                inversion E; subst; now apply activation_observe_start.
    + exfalso; apply (proj2 (@ordinary_evaluation_sides tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) fr
        (Syntax.Side target raw tail) Hpure (proj1 (inv_control Hinv))) target raw tail); reflexivity.
    + pose proof E as Estep; unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; rewrite Hdefer in E; inversion E; subst.
      eapply activation_same_step; [exact Estep|exact Hfront|activation_no_start|apply request_ranking].
  - activation_unchanged E Hfront.
  - activation_unchanged E Hfront.
  - activation_unchanged E Hfront.
  - activation_unchanged E Hfront.
Qed.
Theorem ordinary_activation_frontier tf roots c : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) c -> activation_frontier c.
Proof.
  intros Hdefer Hpure Hpath.
  assert (Hwalk : forall first last, Sem.steps tf first last -> Sem.steps tf (R.initial_config roots) first ->
    activation_frontier first -> activation_frontier last).
  { intros first last H; induction H; intros Hreach Hfront; [exact Hfront|].
    apply IHsteps; [eapply path_extend; eassumption|exact (@activation_frontier_step tf roots a b Hdefer Hpure
      (proj2 (@reachable_invariants tf roots a Hreach)) Hfront H)]. }
  apply (Hwalk _ _ Hpath (@Sem.StepsRefl tf _)); intros owner [rank Hlookup]; discriminate.
Qed.
Corollary ordinary_rhs_materialized tf roots st fr body k : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr body k)) -> fully_materialized st.
Proof.
  intros Hdefer Hpure Hreach; apply (activation_not_start (@ordinary_activation_frontier tf roots _ Hdefer Hpure Hreach)); activation_no_start.
Qed.

(** A draining frame has finished its update. It must retain a certificate
    even while a child or a lower queued owner is still outstanding. *)
Fixpoint unfinished_stack k : list V.t :=
  match k with
  | R.KLoop | R.KSeedLoop _ => []
  | R.KDrain _ rest => unfinished_stack rest
  | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest | R.KDead fr _ _ rest =>
      R.frame_owner fr :: unfinished_stack rest
  end.
Definition unfinished_owners ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => []
  | R.StartEpisode owner k => owner :: unfinished_stack k
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k => R.frame_owner fr :: unfinished_stack k
  | R.RunDrain _ k | R.Return k => unfinished_stack k
  end.
Definition precision_busy c owner := pending (R.cfg_state c) owner \/ In owner (unfinished_owners (R.cfg_control c)).
Definition zero_creation tf st owner := exists direct, tf owner = Syntax.Ret direct /\
  eqv direct D.bottom /\ R.sigma_value st owner = D.bottom.
Record precision_data before after : Prop := {
  precision_values : forall x, R.sigma_value after x = R.sigma_value before x;
  precision_lookups : forall x value, R.semantic_lookup before x = Some value -> R.semantic_lookup after x = Some value;
  precision_readers : forall target owner, S.mem owner (R.lookup_set (R.readers before) target) = true ->
    S.mem owner (R.lookup_set (R.readers after) target) = true
}.
Record precision_motion tf before after : Prop := {
  precision_store : precision_data (R.cfg_state before) (R.cfg_state after);
  precision_work : forall owner, precision_busy before owner -> precision_busy after owner;
  precision_origins : forall owner, solved (R.cfg_state after) owner -> solved (R.cfg_state before) owner \/
    precision_busy after owner \/ zero_creation tf (R.cfg_state after) owner
}.
Lemma precision_data_refl st : precision_data st st.
Proof. constructor; intros; assumption || reflexivity. Qed.
Lemma precision_data_fields before after : R.sigma after = R.sigma before -> R.dormant_bottom after = R.dormant_bottom before ->
  R.readers after = R.readers before -> precision_data before after.
Proof.
  intros Hs Hd Hr; constructor.
  - intro x; unfold R.sigma_value; now rewrite Hs.
  - intros x value H; unfold R.semantic_lookup; now rewrite Hs,Hd.
  - intros target owner H; now rewrite Hr.
Qed.
Lemma precision_data_trans before middle after : precision_data before middle -> precision_data middle after -> precision_data before after.
Proof.
  intros [Hv Hl Hr] [Hv' Hl' Hr']; constructor; [intro x; now rewrite Hv',Hv|intros; eauto|intros; eauto].
Qed.
Lemma precision_data_materialize st target : precision_data st (R.materialize st target).
Proof. constructor; [apply materialize_valuation|apply materialize_lookup|rewrite materialize_readers; trivial]. Qed.
Lemma precision_data_observe st target : precision_data st (R.observe st target).
Proof. apply precision_data_fields; unfold R.observe; destruct (Ranks.observe _ _); reflexivity. Qed.
Lemma precision_data_request st target : precision_data st (R.request_spawn st target).
Proof. apply precision_data_fields; unfold R.request_spawn; destruct (S.mem _ _); reflexivity. Qed.
Lemma precision_data_reset st owner : precision_data st (R.reset_registered_cells st owner).
Proof. apply precision_data_fields; unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity. Qed.
Lemma precision_data_reader st target owner : precision_data st (R.add_reader st target owner).
Proof.
  constructor; try (intros; assumption || reflexivity).
  intros key reader Hin; destruct (V.eq_dec key target) as [->|Hneq].
  - apply reader_mem_add; now right.
  - unfold R.lookup_set,R.add_reader; cbn [R.with_readers R.readers]; now rewrite ML.lookup_update_other.
Qed.
Lemma precision_data_dormant st target : precision_data st (R.remember_dormant st target).
Proof. constructor; [intro x; reflexivity|apply dormant_lookup|intros; assumption]. Qed.
Lemma precision_data_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) -> precision_data st next.
Proof.
  unfold R.complete_get; intro E; inversion E; subst.
  eapply precision_data_trans; [|apply precision_data_materialize].
  eapply precision_data_trans; [|apply precision_data_reader]; apply precision_data_fields; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
Qed.
Lemma ordinary_dirty_get_is_get tf st fr target next next_fr value :
  side_free_store st -> R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  precision_data st next /\ R.frame_owner next_fr = R.frame_owner fr /\
  R.queue next = R.queue st /\ R.deferred_wakes next = R.deferred_wakes st.
Proof.
  intros Hfree; unfold R.dirty_complete_get.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  set (prepared := R.materialize base target).
  assert (Hprepared : side_free_store prepared).
  { unfold prepared,base; apply side_free_materialize; destruct (R.rank_lt _ _ _); exact Hfree. }
  assert (Hdirty : R.try_dirty_read tf prepared (R.frame_owner fr) target = None).
  { unfold R.try_dirty_read; destruct (V.eq_dec _ _); [reflexivity|now rewrite (proj1 (proj2 Hprepared))]. }
  rewrite Hdirty; intro E; inversion E; subst; split.
  - eapply precision_data_trans; [|apply precision_data_reader].
    unfold prepared; eapply precision_data_trans; [|apply precision_data_materialize].
    unfold base; apply precision_data_fields; destruct (R.rank_lt _ _ _); reflexivity.
  - split; [reflexivity|]; unfold prepared,base,R.materialize; destruct (R.rank_lt _ _ _); destruct (M.lookup _ _); now split.
Qed.
Lemma get_precision_fields st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  R.frame_owner next_fr = R.frame_owner fr /\ R.queue next = R.queue st /\ R.deferred_wakes next = R.deferred_wakes st.
Proof.
  unfold R.complete_get; intro E; inversion E; subst; split; [reflexivity|].
  unfold R.materialize; destruct (M.lookup _ _); destruct (R.rank_lt _ _ _); now split.
Qed.
Lemma solved_materialize_origin st target x : solved (R.materialize st target) x -> solved st x \/ x = target.
Proof.
  destruct (V.eq_dec x target) as [->|Hneq]; [intros; now right|].
  unfold R.materialize; destruct (M.lookup (R.sigma st) target); [intros; now left|].
  intros [value H]; left; exists value; unfold R.semantic_lookup in H; cbn in H; rewrite ML.lookup_update_other in H by exact Hneq; exact H.
Qed.
Lemma solved_dormant_origin st target x : solved (R.remember_dormant st target) x -> solved st x \/ x = target.
Proof.
  destruct (V.eq_dec x target) as [->|Hneq]; [intros; now right|].
  intros [value H]; left; exists value; unfold R.semantic_lookup,R.remember_dormant in H; cbn in H.
  unfold R.semantic_lookup; destruct (M.lookup (R.sigma st) x); [exact H|].
  destruct (S.mem x (R.dormant_bottom st)) eqn:E.
  - assert (S.mem x (S.add target (R.dormant_bottom st)) = true) by (apply SL.add_spec; now right).
    now rewrite H0 in H.
  - assert (S.mem x (S.add target (R.dormant_bottom st)) = false).
    { destruct (S.mem x (S.add target (R.dormant_bottom st))) eqn:E'; [|reflexivity].
      apply SL.add_spec in E'; intuition congruence. }
    rewrite H0 in H; discriminate.
Qed.
Definition outside_commit ctrl := match ctrl with R.RunCommit _ _ _ => False|_ => True end.

Ltac ordinary_precision_data Hfree :=
  cbn [R.cfg_state R.cfg_control];
  first
    [ apply precision_data_fields; reflexivity
    | match goal with |- precision_data ?before ?after =>
        eapply (@precision_data_trans before before after); [apply precision_data_refl|];
        apply precision_data_fields; unfold R.observe; destruct (Ranks.observe _ _); reflexivity end
    | match goal with |- precision_data ?before (R.materialize ?base ?target) =>
        eapply (@precision_data_trans before base _); [ordinary_precision_data Hfree|apply precision_data_materialize] end
    | match goal with |- precision_data ?before (R.add_reader ?base ?target ?owner) =>
        eapply (@precision_data_trans before base _); [ordinary_precision_data Hfree|apply precision_data_reader] end
    | apply precision_data_request
    | apply precision_data_reset
    | match goal with |- precision_data ?before (R.remember_dormant ?base ?target) =>
        eapply (@precision_data_trans before base _); [ordinary_precision_data Hfree|apply precision_data_dormant] end
    | match goal with E : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- precision_data ?before ?after =>
        eapply (@precision_data_trans before base after); [|exact (@precision_data_get base fr target next next_fr value E)]; ordinary_precision_data Hfree end
    | match goal with E : R.dirty_complete_get ?tf ?base ?fr ?target = (?next,?next_fr,?value) |- precision_data ?before ?after =>
        let Hbase := fresh "Hfree_base" in
        assert (Hbase : side_free_store base) by (first [exact Hfree|apply side_free_observe; exact Hfree]);
        eapply (@precision_data_trans before base after); [|exact (proj1 (@ordinary_dirty_get_is_get tf base fr target next next_fr value Hbase E))]; ordinary_precision_data Hfree end
    | match goal with E : R.write_side_contribution ?base ?fr ?target ?input = (?next,?changed) |- precision_data ?before ?after =>
        let Hmeta := fresh "Hside_meta" in pose proof (@side_write_metadata base fr target input next changed E) as Hmeta;
        destruct Hmeta as [? [? [? [? _]]]];
        eapply (@precision_data_trans before base after); [ordinary_precision_data Hfree|];
        apply precision_data_fields; cbn [R.enqueue R.mark_side_dirty R.with_queue R.with_dirty_side_targets R.sigma R.dormant_bottom R.readers]; assumption end
    | match goal with |- context [if ?test then _ else _] => destruct test eqn:?; ordinary_precision_data Hfree end
    | progress unfold R.materialize; destruct (M.lookup _ _); ordinary_precision_data Hfree ].
Theorem ordinary_noncommit_data tf before after : side_free_store (R.cfg_state before) -> outside_commit (R.cfg_control before) ->
  R.next_config tf before = Some after -> precision_data (R.cfg_state before) (R.cfg_state after).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hfree Houtside E; try contradiction;
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - inspect_machine_step E; try discriminate; inversion E; subst; ordinary_precision_data Hfree.
  - destruct seeds; inspect_machine_step E; try discriminate; inversion E; subst; ordinary_precision_data Hfree.
  - inspect_machine_step E; try discriminate; inversion E; subst; ordinary_precision_data Hfree.
  - inversion E; subst; cbn; eapply (@precision_data_trans st (R.materialize st owner));
      [apply precision_data_materialize|apply precision_data_fields; reflexivity].
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      inspect_machine_step E; try discriminate; inversion E; subst; ordinary_precision_data Hfree.
  - destruct pending; inspect_machine_step E; try discriminate; inversion E; subst; ordinary_precision_data Hfree.
  - inspect_machine_step E; try discriminate; inversion E; subst; ordinary_precision_data Hfree.
  - destruct k; inspect_machine_step E; try discriminate; inversion E; subst; ordinary_precision_data Hfree.
Qed.

Ltac precision_get_metadata Hfree :=
  repeat match goal with
  | E : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let H := fresh "Hget_fields" in pose proof (@get_precision_fields base fr target next next_fr value E) as H;
      destruct H as [? [? ?]]; clear E
  | E : R.dirty_complete_get ?tf ?base ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let H := fresh "Hget_fields" in let Hb := fresh "Hfree_base" in
      assert (Hb : side_free_store base) by (first [exact Hfree|apply side_free_observe; exact Hfree]);
      pose proof (@ordinary_dirty_get_is_get tf base fr target next next_fr value Hb E) as H;
      destruct H as [_ [? [? ?]]]; clear E
  | E : R.write_side_contribution ?base ?fr ?target ?input = (?next,?changed) |- _ =>
      let H := fresh "Hside_fields" in pose proof (@side_write_metadata base fr target input next changed E) as H;
      destruct H as [_ [_ [_ [_ [? [? _]]]]]]; clear E
  end.
Ltac precision_work_case Hfree E :=
  inspect_machine_step E; try discriminate; inversion E; subst; precision_get_metadata Hfree;
  unfold precision_busy,pending; cbn [R.cfg_state R.cfg_control unfinished_owners unfinished_stack
    R.fresh_frame R.with_frame_side R.with_frame_phase R.frame_owner R.enqueue R.with_queue
    R.with_spawns R.with_readers R.with_dirty_side_targets R.clear_side_dirty R.mark_side_dirty
    R.promote_controlled R.publish_targets R.with_last_targets];
  repeat first
    [ progress rewrite queue_insert_members
    | match goal with H : R.queue ?a = R.queue ?b |- _ => progress rewrite H end
    | match goal with H : R.deferred_wakes ?a = R.deferred_wakes ?b |- _ => progress rewrite H end
    | match goal with H : R.frame_owner ?a = R.frame_owner ?b |- _ => progress rewrite H end
    | match goal with H : R.queue ?a = _ :: _ |- _ => progress rewrite H end
    | match goal with H : R.queue ?a = [] |- _ => progress rewrite H end
    | progress cbn [R.enqueue R.with_queue R.with_spawns R.with_readers R.with_dirty_side_targets
        R.clear_side_dirty R.mark_side_dirty R.promote_controlled R.fresh_frame R.frame_owner]
    | progress unfold R.observe; destruct (Ranks.observe _ _)
    | progress unfold R.materialize; destruct (M.lookup _ _)
    | progress unfold R.request_spawn; destruct (S.mem _ _)
    | progress unfold R.reset_registered_cells; destruct Features.restart_side_phases ];
  repeat match goal with |- context [if ?test then _ else _] => destruct test eqn:? end;
  cbn; repeat rewrite queue_insert_members;
  repeat match goal with H : R.queue ?a = R.queue ?b |- _ => progress rewrite H | H : R.deferred_wakes ?a = R.deferred_wakes ?b |- _ => progress rewrite H end;
  try (unfold R.observe; destruct (Ranks.observe _ _)); cbn;
  repeat match goal with H : R.queue ?a = _ :: _ |- _ => progress rewrite H | H : R.queue ?a = [] |- _ => progress rewrite H end;
  cbn; intuition congruence.
Theorem ordinary_noncommit_work tf before after : Features.defer_spawns = true ->
  side_free_store (R.cfg_state before) -> outside_commit (R.cfg_control before) ->
  R.next_config tf before = Some after -> forall owner, precision_busy before owner -> precision_busy after owner.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hdefer Hfree Houtside E x; try contradiction;
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - precision_work_case Hfree E.
  - destruct seeds; precision_work_case Hfree E.
  - precision_work_case Hfree E.
  - precision_work_case Hfree E.
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      try rewrite Hdefer in E; precision_work_case Hfree E.
  - destruct pending; precision_work_case Hfree E.
  - precision_work_case Hfree E.
  - destruct k; precision_work_case Hfree E.
Qed.

Lemma materialize_other_live st target x : x <> target ->
  R.is_materialized (R.materialize st target) x = R.is_materialized st x.
Proof.
  intro Hneq; unfold R.materialize; destruct (M.lookup (R.sigma st) target); [reflexivity|].
  unfold R.is_materialized; cbn; now rewrite ML.lookup_update_other by exact Hneq.
Qed.
Lemma get_other_live st fr target next next_fr value x : R.complete_get st fr target = (next,next_fr,value) ->
  x <> target -> R.is_materialized next x = R.is_materialized st x.
Proof.
  unfold R.complete_get; intros E Hneq; inversion E; subst; rewrite materialize_other_live by exact Hneq;
    destruct (R.rank_lt _ _ _); reflexivity.
Qed.
Lemma ordinary_dirty_get_other_live tf st fr target next next_fr value x : side_free_store st ->
  R.dirty_complete_get tf st fr target = (next,next_fr,value) -> x <> target ->
  R.is_materialized next x = R.is_materialized st x.
Proof.
  intros Hfree; unfold R.dirty_complete_get.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  set (prepared := R.materialize base target).
  assert (Hprepared : side_free_store prepared).
  { unfold prepared,base; apply side_free_materialize; destruct (R.rank_lt _ _ _); exact Hfree. }
  assert (Hdirty : R.try_dirty_read tf prepared (R.frame_owner fr) target = None).
  { unfold R.try_dirty_read; destruct (V.eq_dec _ _); [reflexivity|now rewrite (proj1 (proj2 Hprepared))]. }
  rewrite Hdirty; intros E Hneq; inversion E; subst; change (R.is_materialized prepared x = R.is_materialized st x).
  unfold prepared; rewrite materialize_other_live by exact Hneq; unfold base; destruct (R.rank_lt _ _ _); reflexivity.
Qed.
Lemma unfinished_framed k x : In x (unfinished_stack k) -> In x (suspended_owners k).
Proof. induction k; cbn; intuition. Qed.
Lemma ready_return_solved_or_pending tf roots st k target :
  invariant tf roots (configuration st (R.Return k)) -> ready (configuration st (R.Return k)) target ->
  solved st target \/ pending st target.
Proof.
  intros Hinv [Hsolved|[Hpending|Hactive]]; [now left|now right|left].
  apply (shape_live_frames (inv_shape Hinv)); exact Hactive.
Qed.

Ltac precision_live_same Hlive :=
  left; apply materialized_solved;
  repeat first [progress cbn [R.with_queue R.with_spawns R.with_readers R.with_dirty_side_targets R.clear_side_dirty
    R.remember_dormant R.with_dormant_bottom R.publish_targets R.with_last_targets R.promote_controlled R.with_controlled R.sigma] in *
  | progress unfold R.observe in *; destruct (Ranks.observe _ _)
  | progress unfold R.request_spawn in *; destruct (S.mem _ _)
  | progress unfold R.reset_registered_cells in *; destruct Features.restart_side_phases
  | match goal with Hlive : context [if ?test then _ else _] |- _ => destruct test eqn:? end ]; cbn [R.is_materialized R.sigma] in Hlive |- *; discriminate || assumption.

Theorem ordinary_noncommit_live tf roots before after : Features.defer_spawns = true ->
  no_side_effects tf -> invariant tf roots before -> side_free_config before -> outside_commit (R.cfg_control before) ->
  R.next_config tf before = Some after -> forall x, R.is_materialized (R.cfg_state after) x = true ->
  solved (R.cfg_state before) x \/ precision_busy after x.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hdefer Hpure Hinv Hfree Houtside E x Hlive; try contradiction;
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - inspect_machine_step E; try discriminate; inversion E; subst; precision_live_same Hlive.
  - destruct seeds; inspect_machine_step E; try discriminate; inversion E; subst; precision_live_same Hlive.
  - inspect_machine_step E; try discriminate; inversion E; subst; precision_live_same Hlive.
  - inversion E; subst; destruct (V.eq_dec x owner) as [->|Hneq].
    + right; right; cbn; now left.
    + left; apply materialized_solved; change (R.is_materialized (R.materialize st owner) x = true) in Hlive;
        now rewrite materialize_other_live in Hlive by exact Hneq.
  - destruct body as [direct|target tail|target raw tail|target tail].
    + inversion E; subst; precision_live_same Hlive.
    + repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
        inspect_machine_step E; try discriminate; inversion E; subst; try precision_live_same Hlive.
      all: cbn [R.cfg_state R.cfg_control] in Hlive |- *.
      all: try (match goal with
      | Eg : R.complete_get ?base ?frame ?key = (?next,?next_fr,?value), Hl : R.is_materialized ?next ?x = true |- _ =>
          destruct (V.eq_dec x key) as [Heq|Hneq];
          [ subst x | rewrite (@get_other_live base frame key next next_fr value x Eg Hneq) in Hl; precision_live_same Hlive ]
      | Eg : R.dirty_complete_get ?sys ?base ?frame ?key = (?next,?next_fr,?value), Hl : R.is_materialized ?next ?x = true |- _ =>
          let Hb := fresh "Hfree_base" in assert (Hb : side_free_store base) by (apply side_free_observe; exact (proj1 Hfree));
          destruct (V.eq_dec x key) as [Heq|Hneq];
          [ subst x | rewrite (@ordinary_dirty_get_other_live sys base frame key next next_fr value x Hb Eg Hneq) in Hl; precision_live_same Hlive ]
      end).
      all: repeat match goal with Eg : context [R.complete_get (if ?test then _ else _) _ _] |- _ => destruct test eqn:? in Eg end.
      all: try (left; apply materialized_solved; match goal with Hmat : R.is_materialized (R.observe ?base ?key) ?key = true |- R.is_materialized ?base ?key = true =>
        unfold R.observe in Hmat; destruct (Ranks.observe _ _); exact Hmat end).
      all: right; left; cbn [R.cfg_state]; match goal with
      | Eg : R.complete_get ?base ?frame ?key = (?next,?next_fr,?value) |- pending ?next ?key =>
          destruct (@get_precision_fields base frame key next next_fr value Eg) as [_ [Hq Hw]];
          unfold pending; rewrite Hq,Hw
      end.
      all: left; unfold R.enqueue; cbn; rewrite queue_insert_members; now left.
    + exfalso; apply (proj2 (@ordinary_evaluation_sides tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) fr
        (Syntax.Side target raw tail) Hpure (proj1 (inv_control Hinv))) target raw tail); reflexivity.
    + rewrite Hdefer in E; inversion E; subst; precision_live_same Hlive.
  - destruct Hfree as [Hs [Hframes [-> Hdead]]]; inversion E; subst; precision_live_same Hlive.
  - inspect_machine_step E; try discriminate; inversion E; subst; precision_live_same Hlive.
  - destruct k as [|seeds|fr target tail k|fr tail k|fr tail k|fr direct pending k|fr k].
    + inversion E; subst; precision_live_same Hlive.
    + inversion E; subst; precision_live_same Hlive.
    + destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:Eg; inversion E; subst; cbn [R.cfg_state] in Hlive.
      destruct (V.eq_dec x target) as [->|Hneq].
      * destruct (@ready_return_solved_or_pending tf roots st (R.KAfterGet fr target tail k) target Hinv
          (proj1 (proj2 (inv_control Hinv)))) as [Hsolved|Hpending]; [now left|].
        right; left; destruct (@get_precision_fields st fr target next next_fr value Eg) as [_ [Hq Hw]];
          unfold pending in *; cbn [R.cfg_state]; now rewrite Hq,Hw.
      * left; apply materialized_solved; now rewrite (@get_other_live st fr target next next_fr value x Eg Hneq) in Hlive.
    + inversion E; subst; precision_live_same Hlive.
    + inversion E; subst; precision_live_same Hlive.
    + destruct Hfree as [_ [_ Hdead]]; contradiction.
    + inversion E; subst; precision_live_same Hlive.
Qed.

Lemma unsolved_value_bottom st owner : R.semantic_lookup st owner = None -> R.sigma_value st owner = D.bottom.
Proof.
  unfold R.semantic_lookup,R.sigma_value; destruct (M.lookup (R.sigma st) owner); [discriminate|reflexivity].
Qed.
Theorem ordinary_noncommit_motion tf roots before after : Features.defer_spawns = true ->
  no_side_effects tf -> invariant tf roots before -> machine_shape tf after -> side_free_config before ->
  outside_commit (R.cfg_control before) -> R.next_config tf before = Some after -> precision_motion tf before after.
Proof.
  intros Hdefer Hpure Hinv Hshape Hfree Houtside Hstep.
  pose proof (@ordinary_noncommit_data tf before after (proj1 Hfree) Houtside Hstep) as Hdata.
  constructor; [exact Hdata|exact (@ordinary_noncommit_work tf before after Hdefer (proj1 Hfree) Houtside Hstep)|].
  intros owner Hsolved; destruct (R.semantic_lookup (R.cfg_state before) owner) eqn:Eold.
  - left; now exists t.
  - apply solved_cases in Hsolved as [[value Hvalue]|Hdormant].
    + assert (Hlive : R.is_materialized (R.cfg_state after) owner = true) by (unfold R.is_materialized; now rewrite Hvalue).
      destruct (@ordinary_noncommit_live tf roots before after Hdefer Hpure Hinv Hfree Houtside Hstep owner Hlive) as [[v H]|Hbusy];
        [rewrite Eold in H; discriminate|now right; left].
    + right; right; pose proof (@shape_dormant tf after Hshape owner Hdormant) as Hpure_owner.
      unfold R.pure_bottom_rhs in Hpure_owner; destruct (tf owner) eqn:E; try discriminate.
      exists t; split; [exact E|split; [now apply equivalent_true|]].
      rewrite (precision_values Hdata); exact (@unsolved_value_bottom (R.cfg_state before) owner Eold).
Qed.

(** Ordinary execution never produces deferred dirty-read wakeups. *)
Lemma ordinary_noncommit_wakes tf before after : side_free_store (R.cfg_state before) ->
  outside_commit (R.cfg_control before) -> R.next_config tf before = Some after ->
  R.deferred_wakes (R.cfg_state after) = R.deferred_wakes (R.cfg_state before).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hfree Houtside E; try contradiction;
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  all: try destruct seeds; try destruct body; try destruct pending.
  all: try match type of E with context [match ?stack with _ => _ end] =>
    lazymatch type of stack with R.continuation => destruct stack end end.
  all: repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end.
  all: inspect_machine_step E; try discriminate; inversion E; subst; precision_get_metadata Hfree;
    cbn [R.cfg_state R.with_queue R.clear_side_dirty R.with_dirty_side_targets R.with_spawns
      R.publish_targets R.with_last_targets R.add_reader R.with_readers R.remember_dormant R.with_dormant_bottom R.deferred_wakes];
    repeat match goal with H : R.deferred_wakes ?a = R.deferred_wakes ?b |- _ => progress rewrite H end;
    repeat first [progress unfold R.observe; destruct (Ranks.observe _ _)
      | progress unfold R.materialize; destruct (M.lookup _ _)
      | progress unfold R.request_spawn; destruct (S.mem _ _)
      | progress unfold R.reset_registered_cells; destruct Features.restart_side_phases
      | match goal with |- context [if ?test then _ else _] => destruct test eqn:? end ];
    cbn [R.deferred_wakes R.enqueue R.with_queue R.with_ranking R.mark_side_dirty R.with_dirty_side_targets];
    repeat match goal with H : R.deferred_wakes ?a = R.deferred_wakes ?b |- _ => progress rewrite H end;
    try (unfold R.observe; destruct (Ranks.observe _ _)); reflexivity.
Qed.
Theorem ordinary_no_wakes tf roots c : no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) c -> R.deferred_wakes (R.cfg_state c) = [].
Proof.
  intros Hpure Hpath.
  assert (Hwalk : forall a b, Sem.steps tf a b -> Sem.steps tf (R.initial_config roots) a ->
    R.deferred_wakes (R.cfg_state a) = [] -> R.deferred_wakes (R.cfg_state b) = []).
  { intros a b H; induction H; intros Hreach Hw; [exact Hw|].
    apply IHsteps; [eapply path_extend; eassumption|].
    pose proof (proj1 (@ordinary_side_free tf roots a Hpure Hreach)) as Hfree.
    destruct a as [st ctrl]; destruct ctrl;
      try (rewrite (@ordinary_noncommit_wakes tf _ _ Hfree I H); exact Hw).
    unfold Sem.step,R.next_config in H; cbn [R.cfg_state R.cfg_control] in H.
    destruct (R.set_value (R.flush_deferred st) f t) as [next next_fr] eqn:E; inversion H; subst.
    cbn [R.cfg_state]; rewrite (proj1 (proj2 (proj2 (proj2 (@set_value_metadata _ _ _ _ _ E))))); reflexivity.
  }
  exact (Hwalk _ _ Hpath (@Sem.StepsRefl tf _) eq_refl).
Qed.
Lemma ordinary_solved_step tf roots before after : no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) before -> R.next_config tf before = Some after ->
  forall x, solved (R.cfg_state before) x -> solved (R.cfg_state after) x.
Proof.
  intros Hpure Hreach Hstep; pose proof (proj1 (@ordinary_side_free tf roots before Hpure Hreach)) as Hfree.
  destruct before as [st ctrl]; destruct ctrl.
  all: try (intros x [value Hvalue]; exists value;
    exact (@precision_lookups _ _ (@ordinary_noncommit_data tf _ _ Hfree I Hstep) x value Hvalue)).
  unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  destruct (R.set_value (R.flush_deferred st) f t) as [next next_fr] eqn:E; inversion Hstep; subst.
  exact (@set_value_solved _ _ _ _ _ E).
Qed.
Lemma ordinary_solved_path tf roots before after : no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) before -> Sem.steps tf before after ->
  forall x, solved (R.cfg_state before) x -> solved (R.cfg_state after) x.
Proof.
  intros Hpure Hreach Hpath; revert Hreach; induction Hpath; intros Hr x Hx; [exact Hx|].
  apply IHHpath; [eapply path_extend; eassumption|exact (@ordinary_solved_step tf roots a b Hpure Hr H x Hx)].
Qed.

Definition reader_targets_solved st := forall target reader,
  S.mem reader (R.lookup_set (R.readers st) target) = true -> solved st target.
Lemma reader_targets_fields before after : R.readers after = R.readers before ->
  (forall x, solved before x -> solved after x) -> reader_targets_solved before -> reader_targets_solved after.
Proof. intros Hr Hlive H target reader Hin; apply Hlive; apply (H target reader); now rewrite <- Hr. Qed.
Lemma reader_targets_add st target owner : solved st target -> reader_targets_solved st ->
  reader_targets_solved (R.add_reader st target owner).
Proof.
  intros Htarget H key reader Hin; destruct (V.eq_dec key target) as [->|Hneq].
  - exact Htarget.
  - unfold R.add_reader,R.lookup_set in Hin; cbn [R.with_readers R.readers] in Hin.
    rewrite ML.lookup_update_other in Hin by exact Hneq; exact (H key reader Hin).
Qed.
Lemma reader_targets_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  reader_targets_solved st -> reader_targets_solved next.
Proof.
  unfold R.complete_get; intro E; inversion E; subst; intros H key reader Hin.
  destruct (V.eq_dec key target) as [->|Hneq].
  - apply materialized_solved,materialize_live.
  - apply materialize_preserves; unfold R.lookup_set in Hin;
      rewrite materialize_readers in Hin;
      cbn [R.with_readers R.readers] in Hin; rewrite ML.lookup_update_other in Hin by exact Hneq.
    destruct (R.rank_lt _ _ _); exact (H key reader Hin).
Qed.
Lemma ordinary_reader_targets_dirty_get tf st fr target next next_fr value : side_free_store st ->
  R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  reader_targets_solved st -> reader_targets_solved next.
Proof.
  intros Hfree; unfold R.dirty_complete_get.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  set (prepared := R.materialize base target).
  assert (Hprepared : side_free_store prepared).
  { unfold prepared,base; apply side_free_materialize; destruct (R.rank_lt _ _ _); exact Hfree. }
  assert (Hdirty : R.try_dirty_read tf prepared (R.frame_owner fr) target = None).
  { unfold R.try_dirty_read; destruct (V.eq_dec _ _); [reflexivity|now rewrite (proj1 (proj2 Hprepared))]. }
  rewrite Hdirty; intros E H; inversion E; subst; apply reader_targets_add.
  - apply materialized_solved,materialize_live.
  - eapply reader_targets_fields; [| |exact H].
    + unfold prepared,base; rewrite materialize_readers; destruct (R.rank_lt _ _ _); reflexivity.
    + unfold prepared,base; intros x Hx; apply materialize_preserves; destruct (R.rank_lt _ _ _); exact Hx.
Qed.
Lemma reader_targets_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  reader_targets_solved st -> reader_targets_solved next.
Proof.
  intros E H key reader Hin; apply (@set_value_solved st fr direct next next_fr E).
  apply (H key reader); exact (@set_value_readers_subset st fr direct next next_fr E key reader Hin).
Qed.
Ltac ordinary_reader_targets Hfree Htargets :=
  cbn [R.cfg_state R.cfg_control] in *;
  let before := match type of Htargets with reader_targets_solved ?st => st end in
  first [exact Htargets
  | match goal with E : R.complete_get ?base ?fr ?target = _ |- _ =>
      eapply reader_targets_get; [exact E|ordinary_reader_targets Hfree Htargets] end
  | match goal with E : R.dirty_complete_get ?tf ?base ?fr ?target = _ |- _ =>
      eapply ordinary_reader_targets_dirty_get; [apply side_free_observe; exact Hfree|exact E|ordinary_reader_targets Hfree Htargets] end
  | match goal with E : R.set_value ?base ?fr ?direct = _ |- _ =>
      eapply reader_targets_commit; [exact E|ordinary_reader_targets Hfree Htargets] end
  | apply reader_targets_add; [first [apply dormant_solves|apply solved_flag; apply orb_true_iff; right; assumption]|ordinary_reader_targets Hfree Htargets]
  | eapply (@reader_targets_fields before _); [reflexivity|intros; assumption|exact Htargets]
  | eapply (@reader_targets_fields before _); [unfold R.observe; destruct (Ranks.observe _ _); reflexivity|intros; assumption|exact Htargets]
  | eapply (@reader_targets_fields before _); [cbn [R.clear_side_dirty R.with_dirty_side_targets R.readers]; rewrite materialize_readers; reflexivity|intros; apply materialize_preserves; assumption|exact Htargets]
  | eapply (@reader_targets_fields before _); [reflexivity|intros; apply dormant_preserves; assumption|exact Htargets]
  | match goal with |- context [if ?test then _ else _] => destruct test eqn:?; ordinary_reader_targets Hfree Htargets end
  | progress unfold R.observe; destruct (Ranks.observe _ _); ordinary_reader_targets Hfree Htargets
  | progress unfold R.request_spawn; destruct (S.mem _ _); ordinary_reader_targets Hfree Htargets
  | progress unfold R.reset_registered_cells; destruct Features.restart_side_phases; ordinary_reader_targets Hfree Htargets
  | progress unfold R.materialize; destruct (M.lookup _ _); ordinary_reader_targets Hfree Htargets].
Theorem ordinary_reader_targets_step tf roots before after : no_side_effects tf ->
  invariant tf roots before -> side_free_config before -> R.next_config tf before = Some after ->
  reader_targets_solved (R.cfg_state before) -> reader_targets_solved (R.cfg_state after).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hpure Hinv Hfree E Htargets; pose proof (proj1 Hfree) as Hstore;
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - inspect_machine_step E; try discriminate; inversion E; subst; ordinary_reader_targets Hstore Htargets.
  - destruct seeds; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      inspect_machine_step E; try discriminate; inversion E; subst; ordinary_reader_targets Hstore Htargets.
  - inspect_machine_step E; try discriminate; inversion E; subst; ordinary_reader_targets Hstore Htargets.
  - inversion E; subst; ordinary_reader_targets Hstore Htargets.
  - destruct body as [direct|target tail|target raw tail|target tail].
    + inversion E; subst; exact Htargets.
    + repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
        inspect_machine_step E; try discriminate; inversion E; subst; ordinary_reader_targets Hstore Htargets.
    + exfalso; eapply (proj2 (@ordinary_evaluation_sides tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) fr
        (Syntax.Side target raw tail) Hpure (proj1 (inv_control Hinv)))); reflexivity.
    + repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
        inspect_machine_step E; try discriminate; inversion E; subst; ordinary_reader_targets Hstore Htargets.
  - destruct Hfree as [_ [_ Hdead]]; change (pending = [] /\ dead_free_stack k) in Hdead; destruct Hdead as [-> _];
      inversion E; subst; ordinary_reader_targets Hstore Htargets.
  - inspect_machine_step E; inversion E; subst; ordinary_reader_targets Hstore Htargets.
  - inspect_machine_step E; try discriminate; inversion E; subst; ordinary_reader_targets Hstore Htargets.
  - destruct k; inspect_machine_step E; try discriminate; inversion E; subst; ordinary_reader_targets Hstore Htargets.
Qed.
Theorem ordinary_reader_targets tf roots c : no_side_effects tf -> Sem.steps tf (R.initial_config roots) c ->
  reader_targets_solved (R.cfg_state c).
Proof.
  intros Hpure Hpath.
  assert (Hwalk : forall a b, Sem.steps tf a b -> Sem.steps tf (R.initial_config roots) a ->
    reader_targets_solved (R.cfg_state a) -> reader_targets_solved (R.cfg_state b)).
  { intros a b H; induction H; intros Hr Htargets; [exact Htargets|].
    apply IHsteps; [eapply path_extend; eassumption|].
    exact (@ordinary_reader_targets_step tf roots a b Hpure (proj2 (@reachable_invariants tf roots a Hr))
      (@ordinary_side_free tf roots a Hpure Hr) H Htargets). }
  apply (Hwalk _ _ Hpath (@Sem.StepsRefl tf _)); intros target reader Hin.
  unfold R.lookup_set in Hin; cbn [R.initial_config R.cfg_state R.empty_state R.readers] in Hin;
    rewrite ML.lookup_empty,SL.empty_spec in Hin; discriminate.
Qed.

(** Episode delimiters follow the executable stack. This local relation is
    independent of value and scheduling laws and is shared by frontier and
    termination arguments. *)
Fixpoint stack_marker owner boundary k : Prop :=
  match k with
  | R.KLoop | R.KSeedLoop _ => False
  | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest
  | R.KDead fr _ _ rest | R.KDrain fr rest =>
      (R.frame_owner fr = owner /\ rest = boundary) \/ stack_marker owner boundary rest
  end.
Definition episode_live owner boundary ctrl :=
  match ctrl with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
  | R.StartEpisode current k => (current = owner /\ k = boundary) \/ stack_marker owner boundary k
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k =>
      (R.frame_owner fr = owner /\ k = boundary) \/ stack_marker owner boundary k
  | R.Return k => stack_marker owner boundary k
  end.
Lemma stack_marker_depth owner boundary k : stack_marker owner boundary k ->
  length (suspended_owners boundary) < length (suspended_owners k).
Proof.
  induction k; cbn [stack_marker suspended_owners]; intros H; try contradiction.
  all: destruct H as [[_ ->]|H]; cbn [length]; [lia|specialize (IHk H); lia].
Qed.
Lemma episode_return_outside owner boundary : ~ episode_live owner boundary (R.Return boundary).
Proof. intro H; pose proof (@stack_marker_depth owner boundary boundary H); lia. Qed.
Lemma stack_marker_owner owner boundary k : stack_marker owner boundary k -> In owner (suspended_owners k).
Proof.
  induction k; cbn [stack_marker suspended_owners]; intros H; try contradiction.
  all: destruct H as [[Heq _]|H]; [subst owner; now left|right; exact (IHk H)].
Qed.
Lemma episode_owner_active owner boundary ctrl : episode_live owner boundary ctrl -> In owner (active_owners ctrl).
Proof.
  destruct ctrl; cbn [episode_live active_owners]; intros H; try contradiction.
  all: try (destruct H as [[-> _]|H]; [now left|right; exact (@stack_marker_owner owner boundary _ H)]).
  exact (@stack_marker_owner owner boundary _ H).
Qed.
Lemma dirty_get_frame_owner tf st fr target next next_fr value :
  R.dirty_complete_get tf st fr target = (next,next_fr,value) -> R.frame_owner next_fr = R.frame_owner fr.
Proof. unfold R.dirty_complete_get; intro E; now inversion E. Qed.
Ltac episode_frame_metadata :=
  repeat match goal with
  | E : R.complete_get ?st ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let Ho := fresh "Hget_owner" in pose proof (proj1 (@get_precision_fields st fr target next next_fr value E)) as Ho; clear E
  | E : R.dirty_complete_get ?tf ?st ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let Ho := fresh "Hget_owner" in pose proof (@dirty_get_frame_owner tf st fr target next next_fr value E) as Ho; clear E
  | E : R.set_value ?st ?fr ?direct = (?next,?next_fr) |- _ =>
      let Ho := fresh "Hcommit_owner" in pose proof (@set_value_owner st fr direct next next_fr E) as Ho; clear E
  end.
Ltac episode_step_case Hstep :=
  inspect_machine_step Hstep; try discriminate; inversion Hstep; subst; episode_frame_metadata;
  cbn [R.cfg_control episode_live stack_marker R.fresh_frame R.with_frame_side R.frame_owner] in *;
  repeat match goal with Ho : R.frame_owner ?after = R.frame_owner ?before |- _ => progress rewrite Ho end;
  intuition eauto.
Theorem episode_boundary_step tf before after owner boundary : episode_live owner boundary (R.cfg_control before) ->
  R.next_config tf before = Some after -> episode_live owner boundary (R.cfg_control after) \/
  exists fr, R.cfg_control before = R.RunDrain fr boundary /\ R.frame_owner fr = owner /\
    R.cfg_control after = R.Return boundary.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|current k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hlive Hstep; cbn [R.cfg_control episode_live] in Hlive; try contradiction;
    unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  - episode_step_case Hstep.
  - destruct body; repeat match type of Hstep with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      episode_step_case Hstep.
  - destruct pending; episode_step_case Hstep.
  - episode_step_case Hstep.
  - inspect_machine_step Hstep; try discriminate; inversion Hstep; subst; episode_frame_metadata;
      cbn [R.cfg_control episode_live stack_marker R.fresh_frame R.frame_owner] in *; intuition eauto.
    all: right; exists fr; repeat split; congruence.
  - destruct k; episode_step_case Hstep.
Qed.

(** Numeric cutoffs include dormant, unranked values at priority zero. They
    let the same barrier account for dormant reads and newly ranked episodes. *)
Lemma priority_grows before after x : rank_extension before after -> priority before x <= priority after x.
Proof.
  intro H; unfold priority; destruct (Ranks.lookup (R.ranking before) x) eqn:E;
    [rewrite (H x n E); lia|destruct (Ranks.lookup (R.ranking after) x); lia].
Qed.
Lemma observe_other_priority st target x : x <> target -> priority (R.observe st target) x = priority st x.
Proof.
  intro Hneq; destruct (Ranks.lookup (R.ranking st) target) as [rank|] eqn:Ht.
  - unfold priority; now rewrite (@observe_existing_ranking st target rank Ht).
  - destruct (Ranks.lookup (R.ranking st) x) as [rank|] eqn:Hx.
    + symmetry; apply priority_extension; [apply observe_extends|now exists rank].
    + unfold R.observe; destruct (Ranks.observe (R.ranking st) target) as [order rank] eqn:E.
      pose proof (@RankLaws.observe_fresh_preserves_absent (R.ranking st) target order rank x Ht E Hneq Hx) as Habsent.
      change (Ranks.lookup order x = None) in Habsent.
      change ((match Ranks.lookup order x with Some n => S n | None => 0 end) = priority st x).
      unfold priority; now rewrite Habsent,Hx.
Qed.
Lemma fresh_priority_above st target x : Ranks.lookup (R.ranking st) target = None ->
  priority st x < priority (R.observe st target) target.
Proof.
  intro Hfresh; destruct (Ranks.lookup (R.ranking st) x) as [rank|] eqn:Hx.
  - assert (Hranked : ranked st x) by now exists rank.
    pose proof (@fresh_discovery_higher st x target Hranked Hfresh) as Hhigher.
    apply (proj1 (@compare_rank (R.observe st target) x target (ranked_extension (observe_extends st target) Hranked)
      (observe_ranks st target))) in Hhigher.
    rewrite <- (@priority_extension st (R.observe st target) x (observe_extends st target) Hranked) in Hhigher; exact Hhigher.
  - unfold priority at 1; rewrite Hx; destruct (observe_ranks st target) as [rank Hrank]; unfold priority; rewrite Hrank; lia.
Qed.
Definition reader_region cutoff st := forall target reader,
  S.mem reader (R.lookup_set (R.readers st) target) = true ->
  priority st reader < cutoff -> priority st target < cutoff.
Definition lower_queue cutoff before after := forall x,
  priority after x < cutoff -> In x (R.queue after) -> In x (R.queue before).
Lemma region_fields cutoff before after : R.ranking after = R.ranking before ->
  R.readers after = R.readers before -> reader_region cutoff before -> reader_region cutoff after.
Proof. intros Hr Hread; unfold reader_region,priority; now rewrite Hr,Hread. Qed.
Lemma region_materialize cutoff st target : reader_region cutoff st -> reader_region cutoff (R.materialize st target).
Proof. eapply region_fields; [apply materialize_ranking|apply materialize_readers]. Qed.
Lemma region_observe_known cutoff st target : ranked st target -> reader_region cutoff st -> reader_region cutoff (R.observe st target).
Proof. intros [rank Hrank]; eapply region_fields; [exact (@observe_existing_ranking st target rank Hrank)|apply observe_readers_table]. Qed.
Lemma region_observe_fresh cutoff st target : Ranks.lookup (R.ranking st) target = None ->
  (forall reader, S.mem reader (R.lookup_set (R.readers st) target) <> true) ->
  reader_region cutoff st -> reader_region cutoff (R.observe st target).
Proof.
  intros Hfresh Hempty Hregion key reader Hin Hlower; rewrite observe_readers_table in Hin.
  destruct (V.eq_dec key target) as [->|Hneq]; [exfalso; exact (Hempty reader Hin)|].
  rewrite observe_other_priority by exact Hneq; apply (Hregion key reader Hin).
  pose proof (@priority_grows st (R.observe st target) reader (observe_extends st target)); lia.
Qed.
Lemma region_at_fresh_episode st target : Ranks.lookup (R.ranking st) target = None ->
  reader_targets_solved st -> ~ solved st target ->
  reader_region (priority (R.observe st target) target) (R.observe st target).
Proof.
  intros Hfresh Htargets Hunsolved key reader Hin _; rewrite observe_readers_table in Hin.
  destruct (V.eq_dec key target) as [->|Hneq].
  - exfalso; apply Hunsolved; exact (Htargets target reader Hin).
  - rewrite observe_other_priority by exact Hneq; exact (@fresh_priority_above st target key Hfresh).
Qed.
Lemma region_add_reader cutoff st target owner : cutoff <= priority st owner -> reader_region cutoff st ->
  reader_region cutoff (R.add_reader st target owner).
Proof.
  intros Howner Hregion key reader Hin Hlower; change (priority st reader < cutoff) in Hlower;
    change (priority st key < cutoff); unfold R.add_reader,R.lookup_set in Hin;
    cbn [R.with_readers R.readers] in Hin; destruct (V.eq_dec key target) as [->|Hneq].
  - rewrite ML.lookup_update_same in Hin; apply SL.add_spec in Hin as [->|Hin]; [cbn in Hlower; lia|exact (Hregion target reader Hin Hlower)].
  - rewrite ML.lookup_update_other in Hin by exact Hneq; exact (Hregion key reader Hin Hlower).
Qed.
Lemma region_get cutoff st fr target next next_fr value : cutoff <= priority st (R.frame_owner fr) ->
  R.complete_get st fr target = (next,next_fr,value) -> reader_region cutoff st -> reader_region cutoff next.
Proof.
  intros Howner E Hregion; unfold R.complete_get in E; inversion E; subst; apply region_materialize.
  apply region_add_reader; [destruct (R.rank_lt _ _ _); exact Howner|].
  destruct (R.rank_lt _ _ _); [exact Hregion|eapply region_fields; [reflexivity|reflexivity|exact Hregion]].
Qed.
Lemma region_dirty_get cutoff tf st fr target next next_fr value : side_free_store st ->
  cutoff <= priority st (R.frame_owner fr) -> R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  reader_region cutoff st -> reader_region cutoff next.
Proof.
  intros Hfree Howner; unfold R.dirty_complete_get.
  set (base := if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target).
  set (prepared := R.materialize base target).
  assert (Hprepared : side_free_store prepared).
  { unfold prepared,base; apply side_free_materialize; destruct (R.rank_lt _ _ _); exact Hfree. }
  assert (Hdirty : R.try_dirty_read tf prepared (R.frame_owner fr) target = None).
  { unfold R.try_dirty_read; destruct (V.eq_dec _ _); [reflexivity|now rewrite (proj1 (proj2 Hprepared))]. }
  rewrite Hdirty; intros E Hregion; inversion E; subst; apply region_add_reader.
  - unfold prepared,base,priority; rewrite materialize_ranking; destruct (R.rank_lt _ _ _); exact Howner.
  - apply region_materialize; unfold base; destruct (R.rank_lt _ _ _); [exact Hregion|eapply region_fields; [reflexivity|reflexivity|exact Hregion]].
Qed.
Lemma region_commit cutoff st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  reader_region cutoff st -> reader_region cutoff next.
Proof.
  intros E Hregion key reader Hin Hlower; pose proof (proj1 (@set_value_metadata st fr direct next next_fr E)) as Hr.
  unfold priority in *; rewrite Hr in *; apply (Hregion key reader).
  - exact (@set_value_readers_subset st fr direct next next_fr E key reader Hin).
  - exact Hlower.
Qed.
Lemma lower_queue_commit cutoff st fr direct next next_fr : cutoff <= priority st (R.frame_owner fr) ->
  reader_region cutoff st -> R.set_value st fr direct = (next,next_fr) -> lower_queue cutoff st next.
Proof.
  intros Howner Hregion E; apply set_value_cases in E as [[_ [-> ->]]|[_ [_ [[_ ->]|[_ ->]]]]];
    try (intros x _ Hin; exact Hin).
  intros x Hlower Hin; change (priority st x < cutoff) in Hlower.
  apply publication_members in Hin as [Hin|[Hin|[-> _]]]; [exact Hin| |lia].
  pose proof (Hregion (R.frame_owner fr) x Hin Hlower); lia.
Qed.
Lemma fresh_unsolved st target : Ranks.lookup (R.ranking st) target = None ->
  R.is_materialized st target = false -> R.is_dormant st target = false -> ~ solved st target.
Proof.
  unfold R.is_materialized,R.is_dormant,solved,Sem.solved,R.semantic_lookup;
    intros Hr; rewrite Hr; destruct (M.lookup (R.sigma st) target); [discriminate|].
  destruct (S.mem target (R.dormant_bottom st)); cbn; intros Hmat Hdormant Hsolved;
    [discriminate|destruct Hsolved as [value Hvalue]; discriminate].
Qed.
Lemma unranked_unmaterialized tf roots c target : invariant tf roots c ->
  Ranks.lookup (R.ranking (R.cfg_state c)) target = None -> R.is_materialized (R.cfg_state c) target = false.
Proof.
  intros Hinv Hr; destruct (R.is_materialized _ _) eqn:E; [|reflexivity].
  destruct (@shape_materialized tf c (inv_shape Hinv) target E) as [rank Hrank]; congruence.
Qed.

(** With deferred spawning, ordinary reads discover higher children and
    never enqueue work themselves. Queue growth is confined to commits. *)
Lemma ordinary_get_queue tf roots st fr target tail k after :
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  side_free_store st -> fully_materialized st ->
  R.next_config tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) = Some after ->
  R.queue (R.cfg_state after) = R.queue st.
Proof.
  intros Hinv Hfree Hfront E.
  assert (Howner : ranked st (R.frame_owner fr)).
  { exact (Forall_inv (shape_stack_ranks (inv_shape Hinv))). }
  unfold R.next_config in E; cbn [configuration R.cfg_state R.cfg_control Syntax.Get] in E.
  destruct (R.is_dormant st target) eqn:Hdormant; [inversion E; reflexivity|].
  destruct (Ranks.lookup (R.ranking st) target) as [rank|] eqn:Hrank.
  - assert (Hmat : R.is_materialized (R.observe st target) target = true).
    { rewrite observe_materialized; apply Hfront; now exists rank. }
    rewrite Hmat in E; destruct (R.dirty_complete_get tf (R.observe st target) fr target) as [[next next_fr] value] eqn:Eget.
    inversion E; subst; cbn [R.cfg_state]; rewrite (proj1 (proj2 (proj2
      (@ordinary_dirty_get_is_get tf (R.observe st target) fr target next next_fr value (@side_free_observe st target Hfree) Eget))));
      unfold R.observe; destruct (Ranks.observe _ _); reflexivity.
  - destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)) eqn:Hbottom.
    + inversion E; reflexivity.
    + assert (Hmat : R.is_materialized (R.observe st target) target = false).
      { rewrite observe_materialized; exact (@unranked_unmaterialized tf roots _ target Hinv Hrank). }
      rewrite Hmat,(@fresh_discovery_higher st (R.frame_owner fr) target Howner Hrank) in E.
      cbn in E; inversion E; subst; cbn [R.cfg_state]; unfold R.observe; destruct (Ranks.observe _ _); reflexivity.
Qed.
Ltac ordinary_queue_administration Hfree Hstep :=
  inspect_machine_step Hstep; try discriminate; inversion Hstep; subst; precision_get_metadata Hfree;
  cbn [R.cfg_state R.queue R.with_queue R.with_spawns R.clear_side_dirty R.with_dirty_side_targets
    R.publish_targets R.with_last_targets R.add_reader R.with_readers R.remember_dormant R.with_dormant_bottom];
  repeat first [progress unfold R.observe; destruct (Ranks.observe _ _)
    | progress unfold R.materialize; destruct (M.lookup _ _)
    | progress unfold R.reset_registered_cells; destruct Features.restart_side_phases
    | progress unfold R.request_spawn; destruct (S.mem _ _)];
  intros x Hin; repeat match goal with H : R.queue ?a = R.queue ?b |- _ => progress rewrite H in Hin end;
  repeat first [progress cbn [R.queue R.with_queue R.with_ranking R.clear_side_dirty R.with_dirty_side_targets] in Hin
    | match goal with H : R.queue ?a = _ :: _ |- _ => progress rewrite H in Hin end
    | match goal with H : R.queue ?a = _ :: _ |- _ => progress rewrite H end
    | progress unfold R.observe in Hin; destruct (Ranks.observe _ _)]; cbn in *;
  repeat match goal with H : R.queue ?a = _ :: _ |- _ => progress rewrite H in Hin end;
  cbn in Hin; intuition congruence.
Theorem ordinary_noncommit_queue_subset tf roots before after : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) before -> outside_commit (R.cfg_control before) ->
  R.next_config tf before = Some after -> forall x, In x (R.queue (R.cfg_state after)) -> In x (R.queue (R.cfg_state before)).
Proof.
  intros Hdefer Hpure Hreach Houtside Hstep.
  pose proof (proj2 (@reachable_invariants tf roots before Hreach)) as Hinv.
  pose proof (@ordinary_side_free tf roots before Hpure Hreach) as Hfree.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    try contradiction; pose proof (proj1 Hfree) as Hstore; pose proof Hstep as E;
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - ordinary_queue_administration Hstore E.
  - destruct seeds; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      ordinary_queue_administration Hstore E.
  - ordinary_queue_administration Hstore E.
  - ordinary_queue_administration Hstore E.
  - destruct body as [direct|target tail|target raw tail|target tail].
    + inversion E; subst; intros; assumption.
    + intros x Hin; rewrite (@ordinary_get_queue tf roots st fr target tail k after Hinv Hstore (@ordinary_rhs_materialized tf roots st fr (Syntax.Get target tail) k Hdefer Hpure Hreach) Hstep) in Hin; exact Hin.
    + exfalso; eapply (proj2 (@ordinary_evaluation_sides tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) fr
        (Syntax.Side target raw tail) Hpure (proj1 (inv_control Hinv)))); reflexivity.
    + rewrite Hdefer in E; ordinary_queue_administration Hstore E.
  - destruct Hfree as [_ [_ Hdead]]; change (pending = [] /\ dead_free_stack k) in Hdead; destruct Hdead as [-> _].
    ordinary_queue_administration Hstore E.
  - ordinary_queue_administration Hstore E.
  - destruct k; ordinary_queue_administration Hstore E.
Qed.

Lemma ordinary_get_region tf roots cutoff st fr target tail k after :
  invariant tf roots (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  side_free_store st -> fully_materialized st -> reader_targets_solved st ->
  cutoff <= priority st (R.frame_owner fr) -> reader_region cutoff st ->
  R.next_config tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) = Some after ->
  reader_region cutoff (R.cfg_state after).
Proof.
  intros Hinv Hfree Hfront Htargets Howner Hregion E.
  assert (Hrank_owner : ranked st (R.frame_owner fr)) by exact (Forall_inv (shape_stack_ranks (inv_shape Hinv))).
  assert (Hobserve_owner : priority (R.observe st target) (R.frame_owner fr) = priority st (R.frame_owner fr)).
  { symmetry; apply priority_extension; [apply observe_extends|exact Hrank_owner]. }
  unfold R.next_config in E; cbn [configuration R.cfg_state R.cfg_control Syntax.Get] in E.
  destruct (R.is_dormant st target) eqn:Hdormant.
  - inversion E; subst; cbn [R.cfg_state]; exact (@region_add_reader cutoff st target (R.frame_owner fr) Howner Hregion).
  - destruct (Ranks.lookup (R.ranking st) target) as [rank|] eqn:Hrank.
    + assert (Hmat : R.is_materialized (R.observe st target) target = true).
      { rewrite observe_materialized; apply Hfront; now exists rank. }
      rewrite Hmat in E; destruct (R.dirty_complete_get tf (R.observe st target) fr target) as [[next next_fr] value] eqn:Eget.
      inversion E; subst; cbn [R.cfg_state]; eapply region_dirty_get; [apply side_free_observe; exact Hfree| |exact Eget|].
      * now rewrite Hobserve_owner.
      * apply region_observe_known; [now exists rank|exact Hregion].
    + assert (Hmat_old : R.is_materialized st target = false) by exact (@unranked_unmaterialized tf roots _ target Hinv Hrank).
      destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)) eqn:Hbottom.
      * inversion E; subst; cbn [R.cfg_state]; apply region_add_reader; [exact Howner|].
        eapply region_fields; [reflexivity|reflexivity|exact Hregion].
      * rewrite observe_materialized,Hmat_old,(@fresh_discovery_higher st (R.frame_owner fr) target Hrank_owner Hrank) in E.
        cbn in E; inversion E; subst; cbn [R.cfg_state]; apply region_observe_fresh; [exact Hrank| |exact Hregion].
        intros reader Hin; apply (@fresh_unsolved st target Hrank Hmat_old Hdormant); exact (Htargets target reader Hin).
Qed.
Lemma active_head_cutoff cutoff st ctrl root : sorted_queue st (active_owners ctrl) ->
  In root (active_owners ctrl) -> cutoff <= priority st root -> forall head tail,
  active_owners ctrl = head :: tail -> cutoff <= priority st head.
Proof.
  intros Hsorted Hin Hcut head tail E; rewrite E in Hsorted,Hin;
    pose proof (@sorted_head_max st head tail root Hsorted Hin); lia.
Qed.
Ltac region_administration cutoff st Hregion Hstep :=
  inspect_machine_step Hstep; try discriminate; inversion Hstep; subst; cbn [R.cfg_state];
  (eapply (@region_fields cutoff st _); [| |exact Hregion];
  repeat first [progress unfold R.materialize; destruct (M.lookup _ _)
    | progress unfold R.request_spawn; destruct (S.mem _ _)
    | progress unfold R.reset_registered_cells; destruct Features.restart_side_phases]; reflexivity).
Theorem ordinary_episode_region_step tf roots cutoff before after root boundary :
  Features.defer_spawns = true -> no_side_effects tf -> Sem.steps tf (R.initial_config roots) before ->
  episode_live root boundary (R.cfg_control before) -> cutoff <= priority (R.cfg_state before) root ->
  reader_region cutoff (R.cfg_state before) -> R.next_config tf before = Some after ->
  reader_region cutoff (R.cfg_state after) /\ lower_queue cutoff (R.cfg_state before) (R.cfg_state after).
Proof.
  intros Hdefer Hpure Hreach Hepisode Hcut Hregion Hstep.
  pose proof (proj2 (@reachable_invariants tf roots before Hreach)) as Hinv.
  pose proof (@ordinary_side_free tf roots before Hpure Hreach) as Hfree.
  pose proof (@ordinary_reader_targets tf roots before Hpure Hreach) as Htargets.
  pose proof (@active_head_cutoff cutoff (R.cfg_state before) (R.cfg_control before) root
    (shape_stack_order (inv_shape Hinv)) (@episode_owner_active root boundary (R.cfg_control before) Hepisode) Hcut) as Hhead.
  split.
  - destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
      try contradiction; pose proof (proj1 Hfree) as Hstore; pose proof Hstep as E;
      unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
    + region_administration cutoff st Hregion E.
    + destruct body as [direct|target tail|target raw tail|target tail].
      * inversion E; subst; exact Hregion.
      * exact (@ordinary_get_region tf roots cutoff st fr target tail k after Hinv Hstore
          (@ordinary_rhs_materialized tf roots st fr (Syntax.Get target tail) k Hdefer Hpure Hreach)
          Htargets (Hhead _ _ eq_refl) Hregion Hstep).
      * exfalso; eapply (proj2 (@ordinary_evaluation_sides tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) fr
          (Syntax.Side target raw tail) Hpure (proj1 (inv_control Hinv)))); reflexivity.
      * rewrite Hdefer in E; region_administration cutoff st Hregion E.
    + destruct Hfree as [_ [_ Hdead]]; change (pending = [] /\ dead_free_stack k) in Hdead; destruct Hdead as [-> _].
      region_administration cutoff st Hregion E.
    + destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:Eset; inversion E; subst.
      exact (@region_commit cutoff (R.flush_deferred st) fr direct next next_fr Eset Hregion).
    + region_administration cutoff st Hregion E.
    + destruct k.
      * contradiction.
      * contradiction.
      * destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Eget; inversion E; subst;
          exact (@region_get cutoff st f t next next_fr value (Hhead _ _ eq_refl) Eget Hregion).
      * region_administration cutoff st Hregion E.
      * region_administration cutoff st Hregion E.
      * region_administration cutoff st Hregion E.
      * region_administration cutoff st Hregion E.
  - destruct (R.cfg_control before) eqn:Hctrl.
    all: try (intros x _ Hin; exact (@ordinary_noncommit_queue_subset tf roots before after Hdefer Hpure Hreach
      ltac:(unfold outside_commit; rewrite Hctrl; exact I) Hstep x Hin)).
    destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in Hctrl; subst ctrl.
    unfold R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
    destruct (R.set_value (R.flush_deferred st) f t) as [next next_fr] eqn:Eset; inversion Hstep; subst; cbn [R.cfg_state].
    intros x Hlower Hin; apply (@lower_queue_commit cutoff (R.flush_deferred st) f t next next_fr
      (Hhead _ _ eq_refl) Hregion Eset x Hlower) in Hin.
    unfold R.flush_deferred in Hin; cbn in Hin; rewrite queue_many_members in Hin;
      destruct Hin as [Hin|Hin]; [|exact Hin].
    pose proof (@ordinary_no_wakes tf roots (configuration st (R.RunCommit f t c)) Hpure Hreach) as Hw;
      cbn [configuration R.cfg_state] in Hw; rewrite Hw in Hin; contradiction.
Qed.

Definition queue_under cutoff st := Forall (fun x => priority st x < cutoff) (R.queue st).
Lemma reset_queue st owner : R.queue (R.reset_registered_cells st owner) = R.queue st.
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity. Qed.
Lemma closing_queue_under tf roots st fr k after :
  invariant tf roots (configuration st (R.RunDrain fr k)) ->
  R.next_config tf (configuration st (R.RunDrain fr k)) = Some after -> R.cfg_control after = R.Return k ->
  queue_under (priority st (R.frame_owner fr)) (R.cfg_state after).
Proof.
  intros Hinv E Hreturn.
  pose proof (shape_queue_order (inv_shape Hinv)) as Hsorted.
  pose proof (shape_queue_ranks (inv_shape Hinv)) as Hranked.
  assert (Howner : ranked st (R.frame_owner fr)) by exact (Forall_inv (shape_stack_ranks (inv_shape Hinv))).
  unfold R.next_config in E; cbn [configuration R.cfg_state R.cfg_control] in E;
    unfold R.queue_peek,R.queue_pop in E; destruct (R.queue st) as [|head rest] eqn:Hqueue.
  - inversion E; subst; unfold queue_under; cbn [R.cfg_state]; rewrite reset_queue,Hqueue; constructor.
  - destruct (V.eq_dec head (R.frame_owner fr)) as [Heq|Hneq].
    + inversion E; subst; discriminate.
    + destruct (R.rank_lt st (R.frame_owner fr) head) eqn:Hlt; [inversion E; subst; discriminate|].
      inversion E; subst; unfold queue_under; cbn [R.cfg_state]; rewrite reset_queue,Hqueue; apply Forall_forall; intros x Hin.
      assert (Hhead : ranked st head).
      { change (ranked_list st (R.queue st)) in Hranked; rewrite Hqueue in Hranked; exact (Forall_inv Hranked). }
      apply (proj1 (@compare_rank_false st (R.frame_owner fr) head Howner Hhead)) in Hlt.
      assert (Hdifferent : priority st head <> priority st (R.frame_owner fr)).
      { intro Hequal; apply Hneq; exact (@priority_distinct st head (R.frame_owner fr) (shape_ranks (inv_shape Hinv)) Hhead Howner Hequal). }
      change (sorted_queue st (R.queue st)) in Hsorted; rewrite Hqueue in Hsorted.
      pose proof (@sorted_head_max st head rest x Hsorted Hin);
      unfold priority at 1; rewrite reset_ranking;
      change (priority st x < priority st (R.frame_owner fr)); lia.
Qed.

Record episode_frontier cutoff root boundary c : Prop := {
  frontier_readers : reader_region cutoff (R.cfg_state c);
  frontier_location : episode_live root boundary (R.cfg_control c) \/ R.cfg_control c = R.Return boundary;
  frontier_root : ranked (R.cfg_state c) root;
  frontier_cutoff : priority (R.cfg_state c) root = cutoff;
  frontier_exit : R.cfg_control c = R.Return boundary -> queue_under cutoff (R.cfg_state c)
}.
Lemma fresh_episode_frontier st root boundary : Ranks.lookup (R.ranking st) root = None ->
  reader_targets_solved st -> ~ solved st root ->
  episode_frontier (priority (R.observe st root) root) root boundary
    (configuration (R.observe st root) (R.StartEpisode root boundary)).
Proof.
  intros Hfresh Htargets Hunsolved; constructor.
  - exact (@region_at_fresh_episode st root Hfresh Htargets Hunsolved).
  - left; left; split; reflexivity.
  - apply observe_ranks.
  - reflexivity.
  - discriminate.
Qed.

Lemma lower_queue_trans cutoff first middle last : rank_extension middle last ->
  lower_queue cutoff first middle -> lower_queue cutoff middle last -> lower_queue cutoff first last.
Proof.
  intros Hr Hfirst Hlast x Hlower Hin; apply Hfirst; [|exact (Hlast x Hlower Hin)].
  pose proof (@priority_grows middle last x Hr); lia.
Qed.
Theorem episode_frontier_step tf roots cutoff root boundary before after :
  Features.defer_spawns = true -> no_side_effects tf -> Sem.steps tf (R.initial_config roots) before ->
  episode_frontier cutoff root boundary before -> R.cfg_control before <> R.Return boundary ->
  R.next_config tf before = Some after ->
  episode_frontier cutoff root boundary after /\ lower_queue cutoff (R.cfg_state before) (R.cfg_state after).
Proof.
  intros Hdefer Hpure Hreach Hfront Hnot Hstep.
  destruct (frontier_location Hfront) as [Hlive|Hreturned]; [|contradiction].
  destruct (@ordinary_episode_region_step tf roots cutoff before after root boundary Hdefer Hpure Hreach Hlive
    ltac:(rewrite (frontier_cutoff Hfront); lia) (frontier_readers Hfront) Hstep) as [Hregion Hqueue].
  pose proof (@step_rank_extension tf before after Hstep) as Hr.
  assert (Hcut : priority (R.cfg_state after) root = cutoff).
  { rewrite <- (@priority_extension _ _ root Hr (frontier_root Hfront)); exact (frontier_cutoff Hfront). }
  split; [constructor|exact Hqueue].
  - exact Hregion.
  - destruct (@episode_boundary_step tf before after root boundary Hlive Hstep) as [Hactive|[fr [_ [_ Hreturn]]]];
      [now left|now right].
  - exact (@ranked_extension _ _ root Hr (frontier_root Hfront)).
  - exact Hcut.
  - intro Hreturn; destruct (@episode_boundary_step tf before after root boundary Hlive Hstep)
      as [Hactive|[fr [Hbefore [Howner _]]]].
    + rewrite Hreturn in Hactive; exfalso; exact (@episode_return_outside root boundary Hactive).
    + destruct before as [st ctrl]; cbn [R.cfg_state R.cfg_control] in Hbefore; subst ctrl.
      rewrite <- (frontier_cutoff Hfront), <- Howner.
      exact (@closing_queue_under tf roots st fr boundary after
        (proj2 (@reachable_invariants tf roots _ Hreach)) Hstep Hreturn).
Qed.

(** A delimited trace stops before executing its caller's continuation. *)
Inductive episode_steps tf boundary : R.config -> R.config -> Prop :=
| EpisodeStop c : episode_steps tf boundary c c
| EpisodeNext first next last : R.cfg_control first <> R.Return boundary ->
    Sem.step tf first next -> episode_steps tf boundary next last -> episode_steps tf boundary first last.
Lemma episode_steps_path tf boundary first last : episode_steps tf boundary first last -> Sem.steps tf first last.
Proof. intro H; induction H; eauto using Sem.steps. Qed.
Theorem episode_frontier_path tf roots cutoff root boundary first last :
  Features.defer_spawns = true -> no_side_effects tf -> Sem.steps tf (R.initial_config roots) first ->
  episode_steps tf boundary first last -> episode_frontier cutoff root boundary first ->
  episode_frontier cutoff root boundary last /\ lower_queue cutoff (R.cfg_state first) (R.cfg_state last).
Proof.
  intros Hdefer Hpure Hreach Hpath; revert Hreach; induction Hpath; intros Hr Hfront.
  - split; [exact Hfront|intros x _ Hin; exact Hin].
  - destruct (@episode_frontier_step tf roots cutoff root boundary first next Hdefer Hpure Hr Hfront H H0) as [Hnext Hqueue].
    destruct (IHHpath (@path_extend tf _ first next Hr H0) Hnext) as [Hlast Hrest].
    split; [exact Hlast|eapply lower_queue_trans; [exact (@path_rank_extension tf next last (@episode_steps_path tf boundary next last Hpath))|exact Hqueue|exact Hrest]].
Qed.

(** Each suspended read keeps the child's exit frontier and the gap between
    that child and its caller. The gap is insensitive to dormant demands. *)
Definition queue_below st owner := queue_under (priority st owner) st.
Definition queue_gap st parent cutoff := forall x, In x (R.queue st) ->
  priority st x < cutoff -> priority st x < priority st parent.
Definition call_frontier parent boundary c := exists root cutoff,
  ranked (R.cfg_state c) parent /\ episode_frontier cutoff root boundary c /\
  queue_gap (R.cfg_state c) parent cutoff.
Lemma observed_queue st target : R.queue (R.observe st target) = R.queue st.
Proof. unfold R.observe; destruct (Ranks.observe _ _); reflexivity. Qed.
Lemma queue_below_observe st parent target : ranked st parent -> ranked_list st (R.queue st) ->
  queue_below st parent -> queue_below (R.observe st target) parent.
Proof.
  intros Hparent Hqueue Hbelow; unfold queue_below,queue_under in *; apply Forall_forall; intros x Hin.
  rewrite observed_queue in Hin.
  rewrite <- (@priority_extension st (R.observe st target) parent (observe_extends st target) Hparent),
    <- (@priority_extension st (R.observe st target) x (observe_extends st target) (proj1 (Forall_forall _ _) Hqueue x Hin)).
  exact (proj1 (Forall_forall _ _) Hbelow x Hin).
Qed.
Lemma queue_below_fresh st root : Ranks.lookup (R.ranking st) root = None ->
  ranked_list st (R.queue st) -> queue_below (R.observe st root) root.
Proof.
  intros Hfresh Hqueue; unfold queue_below,queue_under; apply Forall_forall; intros x Hin.
  rewrite observed_queue in Hin; rewrite <- (@priority_extension st (R.observe st root) x
    (observe_extends st root) (proj1 (Forall_forall _ _) Hqueue x Hin)); exact (@fresh_priority_above st root x Hfresh).
Qed.
Lemma fresh_call_frontier st parent root boundary : ranked st parent -> ranked_list st (R.queue st) ->
  Ranks.lookup (R.ranking st) root = None -> reader_targets_solved st -> ~ solved st root ->
  queue_below st parent -> call_frontier parent boundary (configuration (R.observe st root) (R.StartEpisode root boundary)).
Proof.
  intros Hparent Hqueue Hfresh Htargets Hunsolved Hbelow.
  exists root,(priority (R.observe st root) root); split.
  - exact (@ranked_extension st (R.observe st root) parent (observe_extends st root) Hparent).
  - split; [exact (@fresh_episode_frontier st root boundary Hfresh Htargets Hunsolved)|].
    intros x Hin _; pose proof (@queue_below_observe st parent root Hparent Hqueue Hbelow) as Hafter.
    exact (proj1 (Forall_forall _ _) Hafter x Hin).
Qed.
Lemma call_frontier_return st parent boundary : call_frontier parent boundary (configuration st (R.Return boundary)) -> queue_below st parent.
Proof.
  intros [root [cutoff [_ [Hepisode Hgap]]]]; pose proof (frontier_exit Hepisode eq_refl) as Hexit.
  unfold queue_below,queue_under in *; apply Forall_forall; intros x Hin.
  apply Hgap; [exact Hin|exact (proj1 (Forall_forall _ _) Hexit x Hin)].
Qed.
Lemma call_frontier_step tf roots parent boundary before after : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) before -> call_frontier parent boundary before ->
  R.cfg_control before <> R.Return boundary -> R.next_config tf before = Some after -> call_frontier parent boundary after.
Proof.
  intros Hdefer Hpure Hreach [root [cutoff [Hparent [Hfront Hgap]]]] Hnot Hstep.
  destruct (@episode_frontier_step tf roots cutoff root boundary before after Hdefer Hpure Hreach Hfront Hnot Hstep) as [Hafter Hqueue].
  pose proof (@step_rank_extension tf before after Hstep) as Hr.
  exists root,cutoff; split; [exact (@ranked_extension _ _ parent Hr Hparent)|split; [exact Hafter|]].
  intros x Hin Hlower; rewrite <- (@priority_extension _ _ parent Hr Hparent).
  assert (Hold : In x (R.queue (R.cfg_state before))) by exact (Hqueue x Hlower Hin).
  assert (Hx : ranked (R.cfg_state before) x) by
    exact (proj1 (Forall_forall _ _) (shape_queue_ranks (inv_shape (proj2 (@reachable_invariants tf roots before Hreach)))) x Hold).
  rewrite <- (@priority_extension _ _ x Hr Hx).
  apply Hgap; [exact Hold|pose proof (@priority_grows _ _ x Hr); lia].
Qed.
Fixpoint stack_calls c k : Prop := match k with
  | R.KLoop | R.KSeedLoop _ => True
  | R.KAfterGet fr _ _ rest => call_frontier (R.frame_owner fr) k c /\ stack_calls c rest
  | R.KDrain _ rest => stack_calls c rest
  | R.KAfterSide _ _ _ | R.KAfterSpawn _ _ _ | R.KDead _ _ _ _ => False
  end.
Definition control_calls c := match R.cfg_control c with
  | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
  | R.StartEpisode _ k | R.RunRhs _ _ k | R.RunDead _ _ _ k | R.RunCommit _ _ k
  | R.RunDrain _ k | R.Return k => stack_calls c k end.
Lemma stack_calls_step tf roots before after k : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) before -> R.next_config tf before = Some after -> stack_calls before k ->
  (forall returned, R.cfg_control before = R.Return returned -> length (suspended_owners k) < length (suspended_owners returned)) ->
  stack_calls after k.
Proof.
  intros Hdefer Hpure Hreach Hstep; induction k; cbn [stack_calls]; intros Hcalls Hdepth; try contradiction; try exact I.
  - destruct Hcalls as [Hcall Hrest]; split.
    + eapply call_frontier_step; [exact Hdefer|exact Hpure|exact Hreach|exact Hcall| |exact Hstep].
      intro E; specialize (Hdepth _ E); lia.
    + apply IHk; [exact Hrest|].
      intros returned E; specialize (Hdepth _ E); cbn [suspended_owners length] in Hdepth; lia.
  - apply IHk; [exact Hcalls|].
    intros returned E; specialize (Hdepth _ E); cbn [suspended_owners length] in Hdepth; lia.
Qed.
Definition current_queue_frontier c := match R.cfg_control c with
  | R.RunSeeds _ => R.queue (R.cfg_state c) = []
  | R.StartEpisode owner _ => queue_below (R.cfg_state c) owner
  | R.RunRhs fr _ _ | R.RunDead fr _ _ _ | R.RunCommit fr _ _ => queue_below (R.cfg_state c) (R.frame_owner fr)
  | _ => True end.
Definition ordinary_frontier c := current_queue_frontier c /\ control_calls c.
Lemma popped_below st head rest : sorted_queue st (head :: rest) ->
  queue_below (R.with_queue st rest) head.
Proof.
  intro H; inversion H; subst; unfold queue_below,queue_under; assumption.
Qed.
Lemma queue_below_fields st next owner : R.ranking next = R.ranking st -> R.queue next = R.queue st ->
  queue_below st owner -> queue_below next owner.
Proof. intros Hr Hq; unfold queue_below,queue_under,priority; now rewrite Hr,Hq. Qed.
Lemma queue_below_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  queue_below st (R.frame_owner fr) -> queue_below next (R.frame_owner next_fr).
Proof.
  intros E H; rewrite (proj1 (@get_precision_fields st fr target next next_fr value E)).
  eapply queue_below_fields; [exact (@complete_get_ranking st fr target next next_fr value E)|
    exact (proj1 (proj2 (@get_precision_fields st fr target next next_fr value E)))|exact H].
Qed.
Lemma ordinary_queue_below_dirty_get tf st fr target next next_fr value : side_free_store st ->
  R.dirty_complete_get tf st fr target = (next,next_fr,value) -> queue_below st (R.frame_owner fr) ->
  queue_below next (R.frame_owner next_fr).
Proof.
  intros Hfree E H; destruct (@ordinary_dirty_get_is_get tf st fr target next next_fr value Hfree E) as [_ [Ho [Hq _]]].
  rewrite Ho; eapply queue_below_fields; [exact (@dirty_get_ranking tf st fr target next next_fr value E)|exact Hq|exact H].
Qed.

Theorem ordinary_frontier_step tf roots before after : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) before -> ordinary_frontier before ->
  R.next_config tf before = Some after -> ordinary_frontier after.
Proof.
  intros Hdefer Hpure Hreach [Hcurrent Hcalls] Hstep.
  pose proof (proj2 (@reachable_invariants tf roots before Hreach)) as Hinv.
  pose proof (@ordinary_side_free tf roots before Hpure Hreach) as Hfree.
  pose proof (@ordinary_reader_targets tf roots before Hpure Hreach) as Htargets.
  assert (Hkeep : forall k, stack_calls before k ->
    (forall returned, R.cfg_control before = R.Return returned -> length (suspended_owners k) < length (suspended_owners returned)) ->
    stack_calls after k).
  { intros; eapply stack_calls_step; eassumption. }
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    cbn [current_queue_frontier control_calls R.cfg_state R.cfg_control] in Hcurrent,Hcalls,Hkeep;
    pose proof Hstep as E; unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E;
    unfold ordinary_frontier,current_queue_frontier,control_calls.
  - destruct (R.queue st) as [|head rest] eqn:Hqueue; cbn [R.queue_pop] in E.
    + destruct (R.pending_spawns st); [discriminate|]; inversion E; subst; split; [exact Hqueue|exact I].
    + inversion E; subst; split; [|exact I].
      apply popped_below; pose proof (shape_queue_order (inv_shape Hinv)) as Hsorted;
        change (sorted_queue st (R.queue st)) in Hsorted; now rewrite Hqueue in Hsorted.
  - destruct seeds as [|root rest]; [inversion E; subst; split; exact I|].
    destruct (R.is_materialized st root || R.is_dormant st root).
    + inversion E; subst; split; [exact Hcurrent|exact I].
    + destruct (Ranks.lookup (R.ranking st) root) as [rank|] eqn:Hroot.
      * inversion E; subst; split; [|exact I].
        unfold queue_below,queue_under; cbn [R.cfg_state]; rewrite observed_queue,Hcurrent; constructor.
      * destruct (R.pure_bottom_rhs tf root); inversion E; subst; split; try exact I.
        -- exact Hcurrent.
        -- unfold queue_below,queue_under; cbn [R.cfg_state]; rewrite observed_queue,Hcurrent; constructor.
  - destruct (R.queue st) as [|head rest] eqn:Hqueue; cbn [R.queue_pop] in E; inversion E; subst; split; try exact I.
    + exact Hqueue.
    + apply popped_below; pose proof (shape_queue_order (inv_shape Hinv)) as Hsorted;
        change (sorted_queue st (R.queue st)) in Hsorted; now rewrite Hqueue in Hsorted.
  - inversion E; subst; split.
    + cbn [R.cfg_state R.cfg_control R.fresh_frame R.frame_owner]; eapply queue_below_fields; [| |exact Hcurrent];
        unfold R.materialize; destruct (M.lookup _ _); reflexivity.
    + apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate].
  - assert (Howner : ranked st (R.frame_owner fr)) by exact (Forall_inv (shape_stack_ranks (inv_shape Hinv))).
    pose proof (shape_queue_ranks (inv_shape Hinv)) as Hqueue_rank.
    assert (Hfull : fully_materialized st) by exact (@ordinary_rhs_materialized tf roots st fr body k Hdefer Hpure Hreach).
    destruct body as [direct|target tail|target raw tail|target tail].
    + inversion E; subst; split; [exact Hcurrent|apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate]].
    + destruct (R.is_dormant st target) eqn:Hdormant.
      * inversion E; subst; split; [eapply queue_below_fields; [reflexivity|reflexivity|exact Hcurrent]|].
        apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate].
      * destruct (Ranks.lookup (R.ranking st) target) as [rank|] eqn:Hrank.
        -- assert (Hmat : R.is_materialized (R.observe st target) target = true).
           { rewrite observe_materialized; apply Hfull; now exists rank. }
           rewrite Hmat in E; destruct (R.dirty_complete_get tf (R.observe st target) fr target) as [[next next_fr] value] eqn:Eget.
           inversion E; subst; split.
           ++ exact (@ordinary_queue_below_dirty_get tf (R.observe st target) fr target next next_fr value
               (@side_free_observe st target (proj1 Hfree)) Eget (@queue_below_observe st (R.frame_owner fr) target Howner Hqueue_rank Hcurrent)).
           ++ apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate].
        -- destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)).
           ++ inversion E; subst; split; [eapply queue_below_fields; [reflexivity|reflexivity|exact Hcurrent]|].
              apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate].
           ++ assert (Hmat : R.is_materialized st target = false) by exact (@unranked_unmaterialized tf roots _ target Hinv Hrank).
              rewrite observe_materialized,Hmat,(@fresh_discovery_higher st (R.frame_owner fr) target Howner Hrank) in E.
              cbn in E; inversion E; subst; split.
              ** exact (@queue_below_fresh st target Hrank Hqueue_rank).
              ** cbn [R.cfg_control stack_calls]; split.
                 --- exact (@fresh_call_frontier st (R.frame_owner fr) target (R.KAfterGet fr target tail k)
                     Howner Hqueue_rank Hrank Htargets (@fresh_unsolved st target Hrank Hmat Hdormant) Hcurrent).
                 --- apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate].
    + exfalso; eapply (proj2 (@ordinary_evaluation_sides tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) fr
        (Syntax.Side target raw tail) Hpure (proj1 (inv_control Hinv)))); reflexivity.
    + rewrite Hdefer in E; inversion E; subst; split.
      * eapply queue_below_fields; [apply request_ranking|unfold R.request_spawn; destruct (S.mem _ _); reflexivity|exact Hcurrent].
      * apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate].
  - destruct Hfree as [_ [_ Hdead]]; change (pending = [] /\ dead_free_stack k) in Hdead; destruct Hdead as [-> _].
    inversion E; subst; split; [exact Hcurrent|apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate]].
  - destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:Eset; inversion E; subst; split; [exact I|].
    apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate].
  - inspect_machine_step E; try discriminate; inversion E; subst;
      cbn [R.cfg_state R.cfg_control stack_calls R.fresh_frame R.frame_owner]; split.
    all: try exact I.
    all: try (apply Hkeep; [exact Hcalls|intros returned Hbad; discriminate]).
    all: match goal with Hq : R.queue ?base = ?head :: ?rest |- _ =>
      pose proof (shape_queue_order (inv_shape Hinv)) as Hsorted;
      change (sorted_queue base (R.queue base)) in Hsorted; rewrite Hq in Hsorted;
      first [exact (@popped_below base head rest Hsorted)|
        change (queue_below (R.with_queue base rest) head); exact (@popped_below base head rest Hsorted)] end.
  - destruct k; cbn [stack_calls] in Hcalls.
    + inversion E; subst; split; exact I.
    + inversion E; subst; split; exact I.
    + destruct Hcalls as [Hcall Hrest]; destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Eget.
      inversion E; subst; split.
      * exact (@queue_below_get st f t next next_fr value Eget (@call_frontier_return st (R.frame_owner f) (R.KAfterGet f t r k) Hcall)).
      * apply Hkeep; [exact Hrest|intros returned Hsame; inversion Hsame; subst; cbn [suspended_owners length]; lia].
    + contradiction.
    + contradiction.
    + contradiction.
    + inversion E; subst; split; [exact I|].
      apply Hkeep; [exact Hcalls|intros returned Hsame; inversion Hsame; subst; cbn [suspended_owners length]; lia].
Qed.
Theorem ordinary_frontiers tf roots c : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) c -> ordinary_frontier c.
Proof.
  intros Hdefer Hpure Hpath.
  assert (Hwalk : forall a b, Sem.steps tf a b -> Sem.steps tf (R.initial_config roots) a -> ordinary_frontier a -> ordinary_frontier b).
  { intros a b H; induction H; intros Hr Hfront; [exact Hfront|].
    apply IHsteps; [eapply path_extend; eassumption|exact (@ordinary_frontier_step tf roots a b Hdefer Hpure Hr Hfront H)]. }
  exact (Hwalk _ _ Hpath (@Sem.StepsRefl tf _) (conj eq_refl I)).
Qed.
Corollary ordinary_commit_queue tf roots st fr direct k : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) -> queue_below st (R.frame_owner fr).
Proof. intros Hdefer Hpure Hreach; exact (proj1 (@ordinary_frontiers tf roots _ Hdefer Hpure Hreach)). Qed.

(** Descending waves need replay and a direct-value bound. Spawn completion
    is tracked separately, since FIFO demands may still be pending here. *)
Definition bounded_replay tf st owner := exists direct reads effects,
  Sem.rhs_eval st (tf owner) direct reads effects /\ D.leq direct (R.sigma_value st owner) = true.
Definition value_frontier tf st owner := forall target, ranked st target ->
  priority st owner <= priority st target -> bounded_replay tf st target.
Lemma queue_below_owner_absent st owner : queue_below st owner -> ~ In owner (R.queue st).
Proof.
  intros H Hin; pose proof (proj1 (Forall_forall _ _) H owner Hin) as Hbad;
    change (priority st owner < priority st owner) in Hbad; lia.
Qed.
Lemma ordinary_frontier_quiet tf roots c owner : no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) c -> queue_below (R.cfg_state c) owner -> ~ pending (R.cfg_state c) owner.
Proof.
  intros Hpure Hreach Hbelow [Hqueue|Hwake]; [exact (@queue_below_owner_absent _ owner Hbelow Hqueue)|].
  rewrite (@ordinary_no_wakes tf roots c Hpure Hreach) in Hwake; contradiction.
Qed.
Lemma evaluation_bounded_get tf c fr target tail : ~ pending (R.cfg_state c) (R.frame_owner fr) ->
  evaluation tf c fr (Syntax.Get target tail) -> bounded_replay tf (R.cfg_state c) (R.frame_owner fr) ->
  solved (R.cfg_state c) target.
Proof.
  intros Hquiet [reads [sides [spawns [Hp [Hreads _]]]]] [direct [observed [effects [Hreplay _]]]].
  destruct (@prefix_replay_direct (R.cfg_state c) (tf (R.frame_owner fr)) (Syntax.Get target tail) reads sides spawns Hp
    (@guarded_reads_replay _ _ _ Hquiet Hreads) direct observed effects Hreplay) as [rest [remaining Hget]].
  inversion Hget; subst; unfold solved,Sem.solved; eauto.
Qed.
Lemma evaluation_bounded_ret tf c fr direct : ~ pending (R.cfg_state c) (R.frame_owner fr) ->
  evaluation tf c fr (Syntax.Ret direct) -> bounded_replay tf (R.cfg_state c) (R.frame_owner fr) ->
  D.leq direct (R.sigma_value (R.cfg_state c) (R.frame_owner fr)) = true.
Proof.
  intros Hquiet [reads [sides [spawns [Hp [Hreads _]]]]] [observed [events [effects [Hreplay Hbound]]]].
  destruct (@prefix_replay_direct (R.cfg_state c) (tf (R.frame_owner fr)) (Syntax.Ret direct) reads sides spawns Hp
    (@guarded_reads_replay _ _ _ Hquiet Hreads) observed events effects Hreplay) as [rest [remaining Hret]].
  inversion Hret; subst; exact Hbound.
Qed.
Lemma ordinary_commit_replay tf roots st fr direct k : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) ->
  exists reads effects, Sem.rhs_eval st (tf (R.frame_owner fr)) direct reads effects.
Proof.
  intros Hdefer Hpure Hreach; pose proof (proj2 (@reachable_invariants tf roots _ Hreach)) as Hinv.
  destruct (proj1 (inv_control Hinv)) as [reads [sides [spawns [Hp [Hreads _]]]]].
  exists reads,sides; apply observation_replay with
    (result := {| Sem.Observation.observed_direct := direct; Sem.Observation.observed_reads := reads;
      Sem.Observation.observed_sides := sides; Sem.Observation.observed_spawns := spawns |}).
  - exact (prefix_finish Hp).
  - exact (@guarded_reads_replay st (R.frame_owner fr) reads
      (@ordinary_frontier_quiet tf roots _ (R.frame_owner fr) Hpure Hreach (@ordinary_commit_queue tf roots st fr direct k Hdefer Hpure Hreach)) Hreads).
Qed.
Lemma ordinary_commit_higher_replay tf roots st fr direct k target : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) ->
  solved st target -> priority st (R.frame_owner fr) < priority st target -> bounded_replay tf st target.
Proof.
  intros Hdefer Hpure Hreach Hsolved Hhigher; pose proof (proj2 (@reachable_invariants tf roots _ Hreach)) as Hinv.
  assert (Hidle : ~ busy (configuration st (R.RunCommit fr direct k)) target).
  { intros [[Hqueue|Hwake]|Hactive].
    - pose proof (proj1 (Forall_forall _ _) (@ordinary_commit_queue tf roots st fr direct k Hdefer Hpure Hreach) target Hqueue) as Hbelow.
      change (priority st target < priority st (R.frame_owner fr)) in Hbelow; lia.
    - pose proof (@ordinary_no_wakes tf roots _ Hpure Hreach) as Hw; cbn [configuration R.cfg_state] in Hw, Hwake; rewrite Hw in Hwake; contradiction.
    - pose proof (@sorted_head_max st (R.frame_owner fr) (suspended_owners k) target
        (shape_stack_order (inv_shape Hinv)) Hactive) as Hmax.
      change (priority st target <= priority st (R.frame_owner fr)) in Hmax; lia.
  }
  destruct (inv_summaries Hinv Hsolved) as [Hbusy|[result Hsaved]]; [contradiction|].
  exists (Sem.observed_direct result),(Sem.observed_reads result),(Sem.observed_sides result); split; [|exact (saved_direct Hsaved)].
  apply observation_replay; [exact (saved_trace Hsaved)|].
  apply guarded_reads_replay with target; [intros Hp; apply Hidle; now left|exact (saved_reads Hsaved)].
Qed.
Lemma replay_as_observation st body direct reads effects : Sem.rhs_eval st body direct reads effects ->
  exists result, Sem.observes_at (R.sigma_value st) body result /\
    Sem.observed_direct result = direct /\ Sem.observed_reads result = reads /\ Sem.observed_sides result = effects.
Proof.
  intro Hreplay; destruct (replay_observation Hreplay) as [result [Htrace [Hd [Hr Hs]]]].
  exists result; split; [split; [exact Htrace|]|repeat split; assumption].
  intros x value Hin; change (In (x,value) (Sem.observed_reads result)) in Hin; rewrite Hr in Hin; symmetry; apply lookup_valuation; eapply Sem.rhs_eval_reads_lookup; eassumption.
Qed.
Lemma descending_replay body before after direct reads effects :
  Sem.rhs_dependencies_monotone body -> Sem.rhs_effects_monotone body ->
  (forall x, D.leq (R.sigma_value after x) (R.sigma_value before x) = true) ->
  (forall x, solved before x -> solved after x) -> Sem.rhs_eval before body direct reads effects ->
  exists next_direct next_reads next_effects, Sem.rhs_eval after body next_direct next_reads next_effects /\ D.leq next_direct direct = true.
Proof.
  intros Hdeps Heffects Hvalues Hlive Hreplay.
  destruct (@replay_as_observation before body direct reads effects Hreplay) as [upper [Hupper [Hd [Hr Hs]]]].
  destruct (observation_exists (R.sigma_value after) body) as [lower Hlower].
  assert (Hcommon : Sem.common_read_values_le lower upper).
  { intros x low high Hl Hu; rewrite (proj2 Hlower x low Hl),(proj2 Hupper x high Hu); apply Hvalues. }
  pose proof (Hdeps lower upper (proj1 Hlower) (proj1 Hupper) Hcommon) as Hcoverage.
  assert (Hordered : Sem.valued_events_le (Sem.observed_reads lower) (Sem.observed_reads upper)).
  { intros x low Hl; assert (Hin : In x (map fst (Sem.observed_reads lower))) by (apply in_map_iff; exists (x,low); auto).
    apply Hcoverage in Hin; apply in_map_iff in Hin as [[key high] [Heq Hu]]; cbn in Heq; subst key.
    exists high; split; [exact Hu|exact (Hcommon x low high Hl Hu)]. }
  pose proof (Heffects lower upper (proj1 Hlower) (proj1 Hupper) Hordered) as Heffect.
  exists (Sem.observed_direct lower),(Sem.observed_reads lower),(Sem.observed_sides lower); split.
  - apply observation_replay; [exact (proj1 Hlower)|].
    intros x value Hin; destruct (Hordered x value Hin) as [high [Hhigh _]].
    assert (Hsolved : solved after x).
    { apply Hlive; exists high; eapply Sem.rhs_eval_reads_lookup; [exact Hreplay|now rewrite <- Hr]. }
    rewrite (proj2 Hlower x value Hin); exact (@solved_value after x Hsolved).
  - rewrite <- Hd; exact (Sem.Observation.direct_effect_le Heffect).
Qed.
Lemma bounded_replay_descends tf before after owner : monotonic_system tf ->
  (forall x, D.leq (R.sigma_value after x) (R.sigma_value before x) = true) ->
  (forall x, solved before x -> solved after x) -> R.sigma_value after owner = R.sigma_value before owner ->
  bounded_replay tf before owner -> bounded_replay tf after owner.
Proof.
  intros Hmono Hvalues Hlive Hsame [direct [reads [effects [Hreplay Hbound]]]].
  destruct (@descending_replay (tf owner) before after direct reads effects (proj1 (Hmono owner)) (proj2 (Hmono owner))
    Hvalues Hlive Hreplay) as [next_direct [next_reads [next_effects [Hnext Hbelow]]]].
  exists next_direct,next_reads,next_effects; split; [exact Hnext|rewrite Hsame; eapply DL.leq_trans; eassumption].
Qed.
Lemma value_frontier_static tf before after owner : monotonic_system tf ->
  R.ranking after = R.ranking before -> (forall x, solved before x -> solved after x) ->
  (forall x, R.sigma_value after x = R.sigma_value before x) -> value_frontier tf before owner -> value_frontier tf after owner.
Proof.
  intros Hmono Hr Hlive Hvalues Hfront target Hrank Hhigher.
  unfold ranked in Hrank; unfold priority in Hhigher; rewrite Hr in Hrank,Hhigher.
  eapply bounded_replay_descends; [exact Hmono|intros x; rewrite Hvalues; apply DL.leq_refl|exact Hlive|apply Hvalues|exact (Hfront target Hrank Hhigher)].
Qed.
Lemma commit_descends st fr direct next next_fr :
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
  D.leq (snd (U.update false (R.frame_owner fr) (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
    (D.join direct (R.aggregate st (R.frame_owner fr))))) (R.sigma_value st (R.frame_owner fr)) = true ->
  R.set_value st fr direct = (next,next_fr) -> forall x, D.leq (R.sigma_value next x) (R.sigma_value st x) = true.
Proof.
  intros Hinput Hupdate E x; destruct (V.eq_dec x (R.frame_owner fr)) as [->|Hneq].
  - apply set_value_cases in E as [[_ [-> ->]]|[_ [_ Hresult]]]; [apply DL.leq_refl|].
    destruct (S.mem (R.frame_owner fr) (R.controlled st)) eqn:Hcontrolled; cbn in Hresult.
    + destruct (U.update false _ _ _ _) as [phase value] eqn:Eu; cbn in Hresult,Hupdate.
      destruct Hresult as [[_ ->]|[_ ->]]; [apply DL.leq_refl|rewrite publication_value; exact Hupdate].
    + destruct Hresult as [[_ ->]|[_ ->]]; [apply DL.leq_refl|rewrite publication_value; exact Hinput].
  - rewrite (@set_value_valuation_other st fr direct next next_fr E x Hneq); apply DL.leq_refl.
Qed.
Lemma commit_frontier_descends tf roots st fr direct k next next_fr parent :
  Features.defer_spawns = true -> no_side_effects tf -> monotonic_system tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) ->
  value_frontier tf st parent -> (forall x, D.leq (R.sigma_value next x) (R.sigma_value st x) = true) ->
  R.set_value (R.flush_deferred st) fr direct = (next,next_fr) -> value_frontier tf next parent.
Proof.
  intros Hdefer Hpure Hmono Hreach Hfront Hvalues E target Hrank Hhigher.
  pose proof (proj1 (@set_value_metadata _ _ _ _ _ E)) as Hr; change (R.ranking next = R.ranking st) in Hr.
  unfold ranked in Hrank; unfold priority in Hhigher; rewrite Hr in Hrank,Hhigher.
  destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq].
  - destruct (@ordinary_commit_replay tf roots st fr direct k Hdefer Hpure Hreach) as [reads [effects Hreplay]].
    destruct (@descending_replay (tf (R.frame_owner fr)) st next direct reads effects
      (proj1 (Hmono (R.frame_owner fr))) (proj2 (Hmono (R.frame_owner fr))) Hvalues
      (@set_value_solved _ _ _ _ _ E) Hreplay) as [next_direct [next_reads [next_effects [Hnext Hbelow]]]].
    exists next_direct,next_reads,next_effects; split; [exact Hnext|].
    eapply DL.leq_trans; [exact Hbelow|exact (proj1 (@set_value_bound _ _ _ _ _ E))].
  - eapply bounded_replay_descends; [exact Hmono|exact Hvalues|exact (@set_value_solved _ _ _ _ _ E)|
      exact (@set_value_valuation_other _ _ _ _ _ E target Hneq)|exact (Hfront target Hrank Hhigher)].
Qed.
Lemma new_commit_frontier tf roots st fr direct k next next_fr :
  Features.defer_spawns = true -> no_side_effects tf -> monotonic_system tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) ->
  (forall x, D.leq (R.sigma_value next x) (R.sigma_value st x) = true) ->
  R.set_value (R.flush_deferred st) fr direct = (next,next_fr) -> value_frontier tf next (R.frame_owner fr).
Proof.
  intros Hdefer Hpure Hmono Hreach Hvalues E; apply (@commit_frontier_descends tf roots st fr direct k next next_fr (R.frame_owner fr)); try assumption.
  intros target Hrank Hhigher; destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq].
  - destruct (@ordinary_commit_replay tf roots st fr direct k Hdefer Hpure Hreach) as [reads [effects Hreplay]].
    exists direct,reads,effects; split; [exact Hreplay|].
    eapply DL.leq_trans; [exact (proj1 (@set_value_bound _ _ _ _ _ E))|apply Hvalues].
  - assert (Hsolved : solved st target).
    { apply materialized_solved; apply (activation_not_start (@ordinary_activation_frontier tf roots _ Hdefer Hpure Hreach));
        [activation_no_start|exact Hrank]. }
    eapply ordinary_commit_higher_replay; [exact Hdefer|exact Hpure|exact Hreach|exact Hsolved|].
    assert (Hdifferent : priority st (R.frame_owner fr) <> priority st target).
    { intro Heq; apply Hneq; symmetry; exact (@priority_distinct st (R.frame_owner fr) target
        (shape_ranks (inv_shape (proj2 (@reachable_invariants tf roots _ Hreach))))
        (Forall_inv (shape_stack_ranks (inv_shape (proj2 (@reachable_invariants tf roots _ Hreach))))) Hrank Heq). }
    lia.
Qed.

(** Frame phases survive reads and drain resumptions. A new episode starts
    in the initial phase; only a commit can change an existing phase. *)
Definition phase_origin (before : R.config) (fr : R.frame) :=
  R.frame_phase fr = U.initial_phase false (R.frame_owner fr) \/
  exists old, In old (live_frames (R.cfg_control before)) /\
    R.frame_owner fr = R.frame_owner old /\ R.frame_phase fr = R.frame_phase old.
Lemma get_phase_owner st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  R.frame_owner next_fr = R.frame_owner fr /\ R.frame_phase next_fr = R.frame_phase fr.
Proof. unfold R.complete_get; intro E; now inversion E. Qed.
Lemma dirty_get_phase_owner tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  R.frame_owner next_fr = R.frame_owner fr /\ R.frame_phase next_fr = R.frame_phase fr.
Proof. unfold R.dirty_complete_get; intro E; now inversion E. Qed.
Ltac wave_phase_metadata :=
  repeat match goal with
  | E : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let H := fresh "Hphase_owner" in pose proof (@get_phase_owner base fr target next next_fr value E) as H;
      destruct H as [? ?]; clear E
  | E : R.dirty_complete_get ?tf ?base ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let H := fresh "Hphase_owner" in pose proof (@dirty_get_phase_owner tf base fr target next next_fr value E) as H;
      destruct H as [? ?]; clear E
  end.
Ltac wave_origin_case E :=
  inspect_machine_step E; try discriminate; inversion E; subst; wave_phase_metadata;
  cbn [R.cfg_control live_frames suspended_frames] in *; try contradiction;
  repeat match goal with H : In _ (_ :: _) |- _ => destruct H as [<-|H] end; try contradiction;
  unfold phase_origin; cbn [R.cfg_control live_frames suspended_frames];
  solve [left; reflexivity|
    match goal with |- R.frame_phase ?nextfr = _ \/ _ =>
      right; exists nextfr; repeat split; cbn; tauto end|
    match goal with Ho : R.frame_owner ?nextfr = R.frame_owner ?old, Hp : R.frame_phase ?nextfr = R.frame_phase ?old |- _ =>
      right; exists old; repeat split; cbn; tauto end|
    match goal with |- _ \/ exists old, In old (?head :: ?rest) /\ _ =>
      right; exists head; repeat split; cbn; auto end].
Lemma noncommit_phase_origins tf before after : outside_commit (R.cfg_control before) ->
  R.next_config tf before = Some after -> forall fr, In fr (live_frames (R.cfg_control after)) -> phase_origin before fr.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Houtside E new Hin; try contradiction;
    unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - wave_origin_case E.
  - destruct seeds; wave_origin_case E.
  - wave_origin_case E.
  - wave_origin_case E.
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      wave_origin_case E.
  - destruct pending; wave_origin_case E.
  - wave_origin_case E.
  - destruct k; wave_origin_case E.
Qed.
Lemma live_frames_owners ctrl : map R.frame_owner (live_frames ctrl) = framed_owners ctrl.
Proof.
  assert (Hstack : forall k, map R.frame_owner (suspended_frames k) = suspended_owners k).
  { intro k; induction k; cbn; congruence. }
  destruct ctrl; cbn; auto; now rewrite Hstack.
Qed.
Lemma live_frames_active ctrl fr : In fr (live_frames ctrl) -> In (R.frame_owner fr) (active_owners ctrl).
Proof.
  intro H; assert (Hin : In (R.frame_owner fr) (framed_owners ctrl)).
  { rewrite <- live_frames_owners; apply in_map; exact H. }
  destruct ctrl; cbn [framed_owners active_owners] in *; cbn; tauto.
Qed.
Section DescendingWaves.
Variable wave_safe wave_narrow : U.phase -> Prop.
Hypothesis wave_initial_safe : forall owner, wave_safe (U.initial_phase false owner).
Hypothesis wave_initial_wide : forall owner, ~ wave_narrow (U.initial_phase false owner).
Hypothesis wave_update_safe : forall owner phase old input, wave_safe phase ->
  (wave_narrow phase -> D.leq input old = true) -> wave_safe (fst (U.update false owner phase old input)).
Hypothesis wave_update_narrow : forall owner phase old input, wave_safe phase ->
  wave_narrow (fst (U.update false owner phase old input)) -> D.leq input old = true.
Hypothesis wave_update_descends : forall owner phase old input, wave_safe phase -> D.leq input old = true ->
  D.leq (snd (U.update false owner phase old input)) old = true.
Definition wave_frame tf st fr := wave_safe (R.frame_phase fr) /\
  (wave_narrow (R.frame_phase fr) -> value_frontier tf st (R.frame_owner fr)).
Definition wave_config tf c := Forall (wave_frame tf (R.cfg_state c)) (live_frames (R.cfg_control c)).
Definition some_narrow c := exists fr, In fr (live_frames (R.cfg_control c)) /\ wave_narrow (R.frame_phase fr).
Lemma wave_head_bounded tf roots st fr body k :
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr body k)) ->
  wave_config tf (configuration st (R.RunRhs fr body k)) -> some_narrow (configuration st (R.RunRhs fr body k)) ->
  bounded_replay tf st (R.frame_owner fr).
Proof.
  intros Hreach Hwave [old [Hin Hnarrow]]; pose proof (proj2 (@reachable_invariants tf roots _ Hreach)) as Hinv.
  pose proof (proj1 (Forall_forall _ _) Hwave old Hin) as [_ Hfront]; apply (Hfront Hnarrow).
  - exact (Forall_inv (shape_stack_ranks (inv_shape Hinv))).
  - pose proof (@sorted_head_max st (R.frame_owner fr) (suspended_owners k) (R.frame_owner old)
      (shape_stack_order (inv_shape Hinv)) (@live_frames_active _ old Hin)) as Hmax; exact Hmax.
Qed.
Lemma narrowing_get_solved tf roots st fr target tail k : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  wave_config tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  some_narrow (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) -> solved st target.
Proof.
  intros Hdefer Hpure Hreach Hwave Hnarrow; eapply (@evaluation_bounded_get tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) fr target tail).
  - apply (@ordinary_frontier_quiet tf roots _ (R.frame_owner fr) Hpure Hreach);
      exact (proj1 (@ordinary_frontiers tf roots _ Hdefer Hpure Hreach)).
  - exact (proj1 (inv_control (proj2 (@reachable_invariants tf roots _ Hreach)))).
  - exact (@wave_head_bounded tf roots st fr (Syntax.Get target tail) k Hreach Hwave Hnarrow).
Qed.
Lemma solved_unranked_dormant tf c target : machine_shape tf c ->
  solved (R.cfg_state c) target -> Ranks.lookup (R.ranking (R.cfg_state c)) target = None -> R.is_dormant (R.cfg_state c) target = true.
Proof.
  intros Hshape Hsolved Hrank; destruct (M.lookup (R.sigma (R.cfg_state c)) target) as [value|] eqn:Hlookup.
  - assert (Hmat : R.is_materialized (R.cfg_state c) target = true) by (unfold R.is_materialized; now rewrite Hlookup).
    destruct (shape_materialized Hshape target Hmat) as [n Hn]; congruence.
  - destruct (proj1 (@solved_cases (R.cfg_state c) target) Hsolved) as [[value Hvalue]|Hdormant]; [congruence|].
    unfold R.is_dormant; now rewrite Hlookup,Hdormant,Hrank.
Qed.
Lemma narrowing_step_ranking tf roots before after : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) before -> wave_config tf before -> some_narrow before ->
  R.next_config tf before = Some after -> R.ranking (R.cfg_state after) = R.ranking (R.cfg_state before).
Proof.
  intros Hdefer Hpure Hreach Hwave Hnarrow E;
    pose proof (proj2 (@reachable_invariants tf roots _ Hreach)) as Hinv.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k].
  all: try solve [unfold some_narrow in Hnarrow; cbn [R.cfg_control live_frames] in Hnarrow; destruct Hnarrow as [old [Hin _]]; contradiction].
  all: try solve [eapply unexposed_ranking; [|exact E]; reflexivity].
  destruct body as [direct|target tail|target raw tail|target tail].
  - eapply unexposed_ranking; [|exact E]; reflexivity.
  - assert (Hsolved : solved st target) by exact (@narrowing_get_solved tf roots st fr target tail k Hdefer Hpure Hreach Hwave Hnarrow).
    destruct (R.is_dormant st target) eqn:Hdormant.
    + unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; rewrite Hdormant in E; inversion E; reflexivity.
    + destruct (Ranks.lookup (R.ranking st) target) as [n|] eqn:Hrank.
      * destruct (@ranking_step_view tf _ after E) as [Hsame|[observed [[Heq|Hfalse] Hnew]]]; [exact Hsame| |contradiction].
        cbn in Heq; subst observed; rewrite Hnew; exact (@observe_existing_ranking st target n Hrank).
      * pose proof (@solved_unranked_dormant tf _ target (inv_shape Hinv) Hsolved Hrank) as Hbad;
        change (R.is_dormant st target = true) in Hbad; congruence.
  - exfalso; eapply (proj2 (@ordinary_evaluation_sides tf _ fr (Syntax.Side target raw tail) Hpure (proj1 (inv_control Hinv)))); reflexivity.
  - unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E; rewrite Hdefer in E; inversion E; apply request_ranking.
Qed.
Lemma noncommit_wave_preserves tf roots before after : Features.defer_spawns = true -> no_side_effects tf -> monotonic_system tf ->
  Sem.steps tf (R.initial_config roots) before -> outside_commit (R.cfg_control before) -> wave_config tf before ->
  R.next_config tf before = Some after -> wave_config tf after.
Proof.
  intros Hdefer Hpure Hmono Hreach Houtside Hwave E; apply Forall_forall; intros fr Hin.
  destruct (@noncommit_phase_origins tf before after Houtside E fr Hin) as [Hinitial|[old [Hmember [Howner Hphase]]]].
  - unfold wave_frame; rewrite Hinitial; split; [apply wave_initial_safe|intro Hbad; exfalso; exact (@wave_initial_wide _ Hbad)].
  - destruct (proj1 (Forall_forall _ _) Hwave old Hmember) as [Hsafe Hfront]; unfold wave_frame; rewrite Howner,Hphase; split; [exact Hsafe|intro Hnarrow].
    eapply value_frontier_static; [exact Hmono| |exact (@ordinary_solved_step tf roots before after Hpure Hreach E)| |exact (Hfront Hnarrow)].
    + exact (@narrowing_step_ranking tf roots before after Hdefer Hpure Hreach Hwave (ex_intro _ old (conj Hmember Hnarrow)) E).
    + exact (precision_values (@ordinary_noncommit_data tf before after (proj1 (@ordinary_side_free tf roots before Hpure Hreach)) Houtside E)).
Qed.
Lemma wave_commit_input tf roots st fr direct k : Features.defer_spawns = true -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) ->
  value_frontier tf st (R.frame_owner fr) ->
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true.
Proof.
  intros Hdefer Hpure Hreach Hfront;
    pose proof (proj2 (@reachable_invariants tf roots _ Hreach)) as Hinv.
  assert (Hdirect : D.leq direct (R.sigma_value st (R.frame_owner fr)) = true).
  { eapply (@evaluation_bounded_ret tf (configuration st (R.RunCommit fr direct k)) fr direct); [|exact (proj1 (inv_control Hinv))|].
    - exact (@ordinary_frontier_quiet tf roots _ (R.frame_owner fr) Hpure Hreach (@ordinary_commit_queue tf roots st fr direct k Hdefer Hpure Hreach)).
    - apply Hfront; [exact (Forall_inv (shape_stack_ranks (inv_shape Hinv)))|lia]. }
  pose proof (@ordinary_aggregate_bottom tf roots _ (R.frame_owner fr) Hpure Hreach) as Haggregate;
    change (R.aggregate st (R.frame_owner fr) = D.bottom) in Haggregate.
  apply DL.join_least; [exact Hdirect|rewrite Haggregate; apply DL.bottom_least].
Qed.
Lemma wave_set_safe st fr direct next next_fr : wave_safe (R.frame_phase fr) ->
  (wave_narrow (R.frame_phase fr) -> D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true) ->
  R.set_value st fr direct = (next,next_fr) -> wave_safe (R.frame_phase next_fr).
Proof.
  intros Hsafe Hinput E; apply set_value_cases in E as [[_ [-> ->]]|[_ [Hframe _]]]; [exact Hsafe|].
  rewrite Hframe; destruct (S.mem (R.frame_owner fr) (R.controlled st)); [|exact Hsafe].
  exact (@wave_update_safe (R.frame_owner fr) (R.frame_phase fr) _ _ Hsafe Hinput).
Qed.
Lemma wave_set_descends st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  wave_safe (R.frame_phase fr) ->
  (wave_narrow (R.frame_phase fr) -> D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true) ->
  (wave_narrow (R.frame_phase next_fr) -> D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true) /\
  (D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
    forall x, D.leq (R.sigma_value next x) (R.sigma_value st x) = true).
Proof.
  intros E Hsafe Hinput; split.
  - intro Hnarrow; apply set_value_cases in E as [[Hsame [-> ->]]|[_ [Hphase _]]].
    + exact (proj1 (proj1 (equivalent_true _ _) Hsame)).
    + rewrite Hphase in Hnarrow; destruct (S.mem (R.frame_owner fr) (R.controlled st)); cbn in Hnarrow.
      * eapply wave_update_narrow; eassumption.
      * exact (Hinput Hnarrow).
  - intro Hbelow; apply (@commit_descends st fr direct next next_fr Hbelow); [exact (@wave_update_descends _ _ _ _ Hsafe Hbelow)|exact E].
Qed.
Lemma value_frontier_raise tf st parent owner : priority st parent <= priority st owner ->
  value_frontier tf st parent -> value_frontier tf st owner.
Proof. intros Hbelow Hfront target Hrank Hhigher; apply Hfront; [exact Hrank|lia]. Qed.
Lemma commit_wave_preserves tf roots st fr direct k next next_fr :
  Features.defer_spawns = true -> no_side_effects tf -> monotonic_system tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) ->
  wave_config tf (configuration st (R.RunCommit fr direct k)) ->
  R.set_value (R.flush_deferred st) fr direct = (next,next_fr) ->
  wave_config tf (configuration next (R.RunDrain next_fr k)).
Proof.
  intros Hdefer Hpure Hmono Hreach Hwave E; pose proof (proj2 (@reachable_invariants tf roots _ Hreach)) as Hinv.
  destruct (Forall_inv Hwave) as [Hsafe Hfront].
  assert (Hinput : wave_narrow (R.frame_phase fr) ->
    D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true).
  { intro Hnarrow; exact (@wave_commit_input tf roots st fr direct k Hdefer Hpure Hreach (Hfront Hnarrow)). }
  destruct (@wave_set_descends (R.flush_deferred st) fr direct next next_fr E Hsafe Hinput) as [Hnarrowed Hdescends].
  change (wave_narrow (R.frame_phase next_fr) ->
    D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true) in Hnarrowed.
  change (D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
    forall x, D.leq (R.sigma_value next x) (R.sigma_value st x) = true) in Hdescends.
  unfold wave_config; cbn [R.cfg_control R.cfg_state live_frames]; constructor.
  - split; [exact (@wave_set_safe (R.flush_deferred st) fr direct next next_fr Hsafe Hinput E)|intro Hnarrow].
    rewrite (@set_value_owner _ _ _ _ _ E); exact (@new_commit_frontier tf roots st fr direct k next next_fr Hdefer Hpure Hmono Hreach (Hdescends (Hnarrowed Hnarrow)) E).
  - apply Forall_forall; intros old Hin; destruct (proj1 (Forall_forall _ _) (Forall_inv_tail Hwave) old Hin) as [Holdsafe Holdfront].
    split; [exact Holdsafe|intro Holdnarrow]; eapply commit_frontier_descends; [exact Hdefer|exact Hpure|exact Hmono|exact Hreach|exact (Holdfront Holdnarrow)| |exact E].
    apply Hdescends; apply (@wave_commit_input tf roots st fr direct k Hdefer Hpure Hreach).
    eapply value_frontier_raise; [|exact (Holdfront Holdnarrow)].
    exact (@sorted_head_max st (R.frame_owner fr) (suspended_owners k) (R.frame_owner old)
      (shape_stack_order (inv_shape Hinv)) (@live_frames_active (R.RunCommit fr direct k) old ltac:(cbn; now right))).
Qed.
Theorem ordinary_wave_step tf roots before after : Features.defer_spawns = true -> no_side_effects tf -> monotonic_system tf ->
  Sem.steps tf (R.initial_config roots) before -> wave_config tf before ->
  R.next_config tf before = Some after -> wave_config tf after.
Proof.
  intros Hdefer Hpure Hmono Hreach Hwave E; destruct before as [st ctrl];
    destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k].
  all: try solve [eapply noncommit_wave_preserves; [exact Hdefer|exact Hpure|exact Hmono|exact Hreach|exact I|exact Hwave|exact E]].
  unfold R.next_config in E; cbn [R.cfg_control R.cfg_state] in E;
    destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:Eset; inversion E; subst.
  exact (@commit_wave_preserves tf roots st fr direct k next next_fr Hdefer Hpure Hmono Hreach Hwave Eset).
Qed.
Theorem ordinary_waves tf roots c : Features.defer_spawns = true -> no_side_effects tf -> monotonic_system tf ->
  Sem.steps tf (R.initial_config roots) c -> wave_config tf c.
Proof.
  intros Hdefer Hpure Hmono Hpath.
  assert (Hwalk : forall before after, Sem.steps tf before after -> Sem.steps tf (R.initial_config roots) before ->
    wave_config tf before -> wave_config tf after).
  { intros before after H; induction H; intros Hreach Hwave; [exact Hwave|].
    apply IHsteps; [eapply path_extend; eassumption|exact (@ordinary_wave_step tf roots a b Hdefer Hpure Hmono Hreach Hwave H)]. }
  apply (Hwalk _ _ Hpath (@Sem.StepsRefl tf _)); constructor.
Qed.
Theorem ordinary_wave_admissible tf roots st fr direct k : Features.defer_spawns = true -> no_side_effects tf -> monotonic_system tf ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) ->
  wave_narrow (R.frame_phase fr) ->
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true.
Proof.
  intros Hdefer Hpure Hmono Hreach Hnarrow;
    destruct (Forall_inv (@ordinary_waves tf roots _ Hdefer Hpure Hmono Hreach)) as [_ Hfront].
  exact (@wave_commit_input tf roots st fr direct k Hdefer Hpure Hreach (Hfront Hnarrow)).
Qed.
Theorem ordinary_wave_safe tf roots c : Features.defer_spawns = true -> no_side_effects tf -> monotonic_system tf ->
  Sem.steps tf (R.initial_config roots) c -> Forall (fun fr => wave_safe (R.frame_phase fr)) (live_frames (R.cfg_control c)).
Proof.
  intros Hdefer Hpure Hmono Hreach; eapply Forall_impl; [|exact (@ordinary_waves tf roots c Hdefer Hpure Hmono Hreach)];
    intros fr [Hsafe _]; exact Hsafe.
Qed.
End DescendingWaves.

(** A stable ordinary update certifies a quiet commit. The OneBox
    specialization supplies narrowing laws; it does not instantiate a second
    machine under this proof functor. *)
Module QuietFixedness (UL : UPDATE_LAWS V D U).
Section Narrowing.
Variable narrow : D.t -> D.t -> D.t.
Variable safe : U.phase -> Prop.
Variable narrow_lower : forall old input, D.leq input old = true -> D.leq input (narrow old input) = true.
Variable narrow_upper : forall old input, D.leq input old = true -> D.leq (narrow old input) old = true.
Variable narrowing_update : forall owner phase old input, safe phase -> D.leq input old = true ->
  eqv (snd (U.update false owner phase old input)) (narrow old input).
Definition fixed old input := eqv (narrow old input) old.
Lemma equivalent_input_fixed old input : eqv old input -> fixed old input.
Proof.
  intros [Hleft Hright]; split; [exact (@narrow_upper old input Hright)|].
  eapply DL.leq_trans; [exact Hleft|exact (@narrow_lower old input Hright)].
Qed.
Lemma stable_update_fixed owner phase old input next value direct :
  U.update false owner phase old input = (next,value) -> eqv value old ->
  safe next -> eqv direct input -> fixed old direct.
Proof.
  intros E Hstable Hsafe Heqinput.
  pose proof (@UL.update_stutter_closed false owner phase old input) as Hstutter;
    rewrite E in Hstutter; cbn in Hstutter.
  specialize (Hstutter Hstable old direct (eqv_refl old) Heqinput).
  pose proof (UL.update_sound false owner phase old input) as Hsound; rewrite E in Hsound; cbn in Hsound.
  assert (Hbelow : D.leq direct old = true).
  { eapply DL.leq_trans; [exact (proj1 Heqinput)|eapply DL.leq_trans; [exact Hsound|exact (proj1 Hstable)]]. }
  eapply eqv_trans; [apply eqv_sym; exact (@narrowing_update owner next old direct Hsafe Hbelow)|exact Hstutter].
Qed.
Theorem quiet_commit_fixed st fr direct next next_fr : Features.recompute_controlled = true ->
  R.aggregate st (R.frame_owner fr) = D.bottom -> R.set_value st fr direct = (next,next_fr) ->
  safe (R.frame_phase next_fr) -> ~ pending next (R.frame_owner fr) ->
  fixed (R.sigma_value next (R.frame_owner fr)) direct.
Proof.
  intros Hon Haggregate Hset Hsafe Hquiet.
  set (owner := R.frame_owner fr) in *.
  set (old := R.sigma_value st owner) in *.
  set (candidate := D.join direct (R.aggregate st owner)).
  assert (Hcandidate : eqv candidate direct).
  { unfold candidate; rewrite Haggregate; apply join_bottom_right. }
  apply set_value_cases in Hset as [[Heq [-> ->]]|[Hdifferent [Hframe Hresult]]].
  - apply equivalent_input_fixed; apply eqv_sym.
    eapply eqv_trans; [apply eqv_sym; exact Hcandidate|now apply equivalent_true].
  - fold owner old candidate in Hframe,Hresult; destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled.
    + destruct (U.update false owner (R.frame_phase fr) old candidate) as [phase value] eqn:E;
        cbn in Hframe,Hresult; rewrite Hframe in Hsafe; cbn [R.with_frame_phase R.frame_phase] in Hsafe.
      destruct Hresult as [[Heq ->]|[_ ->]].
      * exact (@stable_update_fixed owner (R.frame_phase fr) old candidate phase value direct E
          (proj1 (equivalent_true value old) Heq) Hsafe (eqv_sym Hcandidate)).
      * exfalso; apply Hquiet; left; apply publication_recomputes; assumption.
    + cbn in Hframe,Hresult; destruct Hresult as [[Heq ->]|[_ ->]].
      * apply equivalent_input_fixed; apply eqv_sym; eapply eqv_trans;
          [apply eqv_sym; exact Hcandidate|now apply equivalent_true].
      * rewrite publication_value; apply equivalent_input_fixed; exact Hcandidate.
Qed.
(** Certificates remain attached to completed owners while their frames drain. *)
Definition precision_certificate tf c owner := exists result,
  Sem.rhs_observes (tf owner) result /\ reads_guarded (R.cfg_state c) owner (Sem.observed_reads result) /\
  fixed (R.sigma_value (R.cfg_state c) owner) (Sem.observed_direct result).
Definition precision_summaries tf c := forall owner, solved (R.cfg_state c) owner ->
  precision_busy c owner \/ precision_certificate tf c owner.
Lemma precision_busy_dec c owner : {precision_busy c owner}+{~ precision_busy c owner}.
Proof.
  unfold precision_busy,pending; destruct (in_dec V.eq_dec owner (R.queue (R.cfg_state c)));
    destruct (in_dec V.eq_dec owner (R.deferred_wakes (R.cfg_state c)));
    destruct (in_dec V.eq_dec owner (unfinished_owners (R.cfg_control c))); intuition.
Qed.
Lemma precision_initial tf roots : precision_summaries tf (R.initial_config roots).
Proof.
  intros owner [value H]; change (R.semantic_lookup R.empty_state owner = Some value) in H;
    rewrite empty_lookup in H; discriminate.
Qed.
Lemma precision_noncommit_preserves tf before after : precision_motion tf before after ->
  precision_summaries tf before -> precision_summaries tf after.
Proof.
  intros Hmotion Hsaved owner Hsolved; destruct (precision_busy_dec after owner) as [Hbusy|Hquiet]; [now left|right].
  destruct (precision_origins Hmotion Hsolved) as [Hold|[Hbusy|[direct [Hret [Heq Hbottom]]]]].
  - destruct (Hsaved owner Hold) as [Hbusy|[result [Htrace [Hreads Hfixed]]]].
    { exfalso; apply Hquiet; exact (precision_work Hmotion Hbusy). }
    exists result; split; [exact Htrace|split].
    + intros target value Hin; destruct (Hreads target value Hin) as [Hpending|[Hlookup Hreader]].
      * exfalso; apply Hquiet; apply (precision_work Hmotion); now left.
      * right; split; [exact (@precision_lookups (R.cfg_state before) (R.cfg_state after) (precision_store Hmotion) target value Hlookup)|
          exact (@precision_readers (R.cfg_state before) (R.cfg_state after) (precision_store Hmotion) target owner Hreader)].
    + rewrite (precision_values (precision_store Hmotion)); exact Hfixed.
  - contradiction.
  - exists {| Sem.Observation.observed_direct := direct; Sem.Observation.observed_reads := [];
      Sem.Observation.observed_sides := []; Sem.Observation.observed_spawns := [] |}.
    split; [rewrite Hret; constructor|split; [intros target value Hin; contradiction|]].
    cbn; rewrite Hbottom; apply equivalent_input_fixed; now apply eqv_sym.
Qed.
Lemma precision_commit_preserves tf roots st fr direct k next next_fr :
  Features.recompute_controlled = true -> R.aggregate (R.flush_deferred st) (R.frame_owner fr) = D.bottom ->
  R.set_value (R.flush_deferred st) fr direct = (next,next_fr) -> safe (R.frame_phase next_fr) ->
  invariant tf roots (configuration st (R.RunCommit fr direct k)) ->
  precision_summaries tf (configuration st (R.RunCommit fr direct k)) ->
  precision_summaries tf (configuration next (R.RunDrain next_fr k)).
Proof.
  intros Hon Haggregate E Hsafe Hinv Hprecision owner Hsolved.
  destruct (precision_busy_dec (configuration next (R.RunDrain next_fr k)) owner) as [Hbusy|Hquiet]; [now left|right].
  destruct (V.eq_dec owner (R.frame_owner fr)) as [->|Hneq].
  - destruct (proj1 (inv_control Hinv)) as [reads [sides [spawns [Hp [Hreads _]]]]].
    exists {| Sem.Observation.observed_direct := direct; Sem.Observation.observed_reads := reads;
      Sem.Observation.observed_sides := sides; Sem.Observation.observed_spawns := spawns |}.
    split; [exact (prefix_finish Hp)|split].
    + intros target value Hin; exact (@set_value_read_guard (R.flush_deferred st) fr direct next next_fr E
        (R.frame_owner fr) target value (@read_guard_flush st (R.frame_owner fr) target value (Hreads target value Hin))).
    + exact (@quiet_commit_fixed (R.flush_deferred st) fr direct next next_fr Hon Haggregate E Hsafe
        (fun H => Hquiet (or_introl H))).
  - assert (Hold : solved st owner).
    { destruct Hsolved as [value H]; exists value; change (R.semantic_lookup next owner = Some value) in H.
      rewrite (@set_value_other_lookup (R.flush_deferred st) fr direct next next_fr E owner Hneq) in H; exact H. }
    destruct (Hprecision owner Hold) as [[Hpending|Hunfinished]|[result [Htrace [Hreads Hfixed]]]].
    + exfalso; apply Hquiet; left; exact (@set_value_pending (R.flush_deferred st) fr direct next next_fr E owner
        (proj2 (flush_pending st owner) Hpending)).
    + exfalso; apply Hquiet; right; change (In owner (R.frame_owner fr :: unfinished_stack k)) in Hunfinished.
      change (In owner (unfinished_stack k)); destruct Hunfinished as [Hsame|Htail]; [congruence|exact Htail].
    + exists result; split; [exact Htrace|split].
      * intros target value Hin; exact (@set_value_read_guard (R.flush_deferred st) fr direct next next_fr E
          owner target value (@read_guard_flush st owner target value (Hreads target value Hin))).
      * cbn [configuration R.cfg_state]; rewrite (@set_value_valuation_other (R.flush_deferred st) fr direct next next_fr E owner Hneq); exact Hfixed.
Qed.
Definition safe_commit c := match R.cfg_control c with
  | R.RunCommit fr direct _ => safe (R.frame_phase (snd (R.set_value (R.flush_deferred (R.cfg_state c)) fr direct)))
  | _ => True end.
Theorem ordinary_precision_reachable tf roots c : Features.recompute_controlled = true -> Features.defer_spawns = true ->
  no_side_effects tf -> (forall before, Sem.steps tf (R.initial_config roots) before -> safe_commit before) ->
  Sem.steps tf (R.initial_config roots) c -> precision_summaries tf c.
Proof.
  intros Hon Hdefer Hpure Hsafe Hpath.
  assert (Hwalk : forall first last, Sem.steps tf first last -> Sem.steps tf (R.initial_config roots) first ->
    precision_summaries tf first -> precision_summaries tf last).
  { intros first last H; induction H; intros Hreach Hprecision; [exact Hprecision|].
    apply IHsteps; [eapply path_extend; eassumption|].
    pose proof (proj2 (@reachable_invariants tf roots a Hreach)) as Hinv.
    pose proof (@ordinary_side_free tf roots a Hpure Hreach) as Hfree.
    pose proof (@path_extend tf _ a b Hreach H) as Hreach_b.
    destruct a as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
      try (eapply precision_noncommit_preserves; [exact (@ordinary_noncommit_motion tf roots _ _ Hdefer Hpure Hinv
        (inv_shape (proj2 (@reachable_invariants tf roots b Hreach_b))) Hfree I H)|exact Hprecision]).
    unfold Sem.step,R.next_config in H; cbn [R.cfg_state R.cfg_control] in H.
    destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:E; inversion H; subst.
    eapply precision_commit_preserves; [exact Hon| |exact E| |exact Hinv|exact Hprecision].
    - exact (@ordinary_aggregate_bottom tf roots (configuration st (R.RunCommit fr direct k))
        (R.frame_owner fr) Hpure Hreach).
    - specialize (Hsafe _ Hreach); unfold safe_commit in Hsafe; cbn in Hsafe; rewrite E in Hsafe; exact Hsafe.
  }
  exact (Hwalk _ _ Hpath (@Sem.StepsRefl tf _) (@precision_initial tf roots)).
Qed.
Theorem fixed_at_quiescence tf st : Sem.quiescent st -> precision_summaries tf (Sem.terminal_config st) ->
  narrowing_fixed_with narrow (fun _ _ direct => direct) tf st.
Proof.
  intros [Hq [Hw Hspawns]] Hprecision owner Hsolved.
  destruct (Hprecision owner Hsolved) as [Hbusy|[result [Htrace [Hreads Hfixed]]]].
  { unfold precision_busy,pending,Sem.terminal_config,unfinished_owners in Hbusy; cbn in Hbusy; rewrite Hq,Hw in Hbusy; cbn in Hbusy; tauto. }
  assert (Hreplay : Sem.rhs_eval st (tf owner) (Sem.observed_direct result) (Sem.observed_reads result) (Sem.observed_sides result)).
  { apply observation_replay; [exact Htrace|apply guarded_reads_replay with owner; [unfold pending; rewrite Hq,Hw; tauto|exact Hreads]]. }
  split; [eexists _,_,_; exact Hreplay|].
  intros direct reads effects Hother; destruct (@replay_unique st (tf owner)
    (Sem.observed_direct result) (Sem.observed_reads result) (Sem.observed_sides result)
    direct reads effects Hreplay Hother) as [<- _]; exact Hfixed.
Qed.
Theorem successful_run_fixed_from_safe_commits fuel tf roots final : Features.recompute_controlled = true -> Features.defer_spawns = true ->
  no_side_effects tf -> (forall c, Sem.steps tf (R.initial_config roots) c -> safe_commit c) ->
  R.solve_fuel fuel tf roots = Some final -> narrowing_fixed_with narrow (fun _ _ direct => direct) tf final.
Proof.
  intros Hon Hdefer Hpure Hsafe Hrun; destruct (@successful_path fuel tf roots final Hrun) as [Hpath Hquiet].
  apply fixed_at_quiescence; [exact Hquiet|exact (@ordinary_precision_reachable tf roots _ Hon Hdefer Hpure Hsafe Hpath)].
Qed.

Section PhasePropagation.
Variable admissible : U.phase -> D.t -> D.t -> Prop.
Variable initial_safe : forall owner, safe (U.initial_phase false owner).
Variable update_safe : forall owner phase old input, safe phase -> admissible phase old input ->
  safe (fst (U.update false owner phase old input)).
Definition frame_safe fr := safe (R.frame_phase fr).
Definition control_safe ctrl := Forall frame_safe (live_frames ctrl).
Definition current_admissible c := match R.cfg_control c with
  | R.RunCommit fr direct _ => admissible (R.frame_phase fr)
      (R.sigma_value (R.cfg_state c) (R.frame_owner fr))
      (D.join direct (R.aggregate (R.cfg_state c) (R.frame_owner fr)))
  | _ => True end.
Lemma get_phase st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  R.frame_phase next_fr = R.frame_phase fr.
Proof. unfold R.complete_get; intro E; now inversion E. Qed.
Lemma dirty_get_phase tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  R.frame_phase next_fr = R.frame_phase fr.
Proof. unfold R.dirty_complete_get; intro E; now inversion E. Qed.
Lemma set_value_phase_safe st fr direct next next_fr : frame_safe fr ->
  admissible (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
    (D.join direct (R.aggregate st (R.frame_owner fr))) ->
  R.set_value st fr direct = (next,next_fr) -> frame_safe next_fr.
Proof.
  intros Hsafe Hadmissible E; apply set_value_cases in E as [[_ [-> ->]]|[_ [Hframe _]]]; [exact Hsafe|].
  unfold frame_safe; rewrite Hframe; destruct (S.mem (R.frame_owner fr) (R.controlled st));
    [cbn; exact (@update_safe (R.frame_owner fr) (R.frame_phase fr)
      (R.sigma_value st (R.frame_owner fr)) (D.join direct (R.aggregate st (R.frame_owner fr))) Hsafe Hadmissible)|exact Hsafe].
Qed.
Ltac phase_metadata :=
  repeat match goal with
  | Eget : R.complete_get ?st ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let H := fresh "Hphase" in pose proof (@get_phase st fr target next next_fr value Eget) as H; clear Eget
  | Eget : R.dirty_complete_get ?tf ?st ?fr ?target = (?next,?next_fr,?value) |- _ =>
      let H := fresh "Hphase" in pose proof (@dirty_get_phase tf st fr target next next_fr value Eget) as H; clear Eget
  end.
Ltac phase_control_case Hstep :=
  inspect_machine_step Hstep; try discriminate; inversion Hstep; subst; phase_metadata;
  unfold control_safe in *; cbn [R.cfg_control live_frames suspended_frames] in *;
  repeat match goal with H : Forall _ (_ :: _) |- _ =>
    let Hfr := fresh "Hframe_safe" in let Hrest := fresh "Hframes_safe" in
    pose proof (Forall_inv H) as Hfr; pose proof (Forall_inv_tail H) as Hrest; clear H end;
  repeat constructor; unfold frame_safe;
  cbn [R.fresh_frame R.with_frame_side R.with_frame_phase R.with_frame_read R.frame_phase];
  repeat match goal with H : R.frame_phase ?a = R.frame_phase ?b |- _ => progress rewrite H end;
  auto using initial_safe.
Theorem safe_control_step tf before after : current_admissible before -> control_safe (R.cfg_control before) ->
  R.next_config tf before = Some after -> control_safe (R.cfg_control after).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hadmissible Hsafe E; unfold R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - phase_control_case E.
  - destruct seeds; phase_control_case E.
  - phase_control_case E.
  - phase_control_case E.
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      phase_control_case E.
  - destruct pending; phase_control_case E.
  - destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:Eset; inversion E; subst.
    unfold control_safe in *; cbn [R.cfg_control live_frames] in *; constructor; [|exact (Forall_inv_tail Hsafe)].
    exact (@set_value_phase_safe (R.flush_deferred st) fr direct next next_fr (Forall_inv Hsafe) Hadmissible Eset).
  - phase_control_case E.
  - destruct k; phase_control_case E.
Qed.
Theorem reachable_control_safe tf roots c : (forall before, Sem.steps tf (R.initial_config roots) before -> current_admissible before) ->
  Sem.steps tf (R.initial_config roots) c -> control_safe (R.cfg_control c).
Proof.
  intros Hadmissible Hpath.
  assert (Hwalk : forall first last, Sem.steps tf first last -> Sem.steps tf (R.initial_config roots) first ->
    control_safe (R.cfg_control first) -> control_safe (R.cfg_control last)).
  { intros first last H; induction H; intros Hreach Hsafe; [exact Hsafe|].
    apply IHsteps; [eapply path_extend; eassumption|exact (@safe_control_step tf a b (Hadmissible a Hreach) Hsafe H)]. }
  apply (Hwalk _ _ Hpath (@Sem.StepsRefl tf _)); constructor.
Qed.
Theorem reachable_commit_safe tf roots :
  (forall before, Sem.steps tf (R.initial_config roots) before -> current_admissible before) ->
  forall c, Sem.steps tf (R.initial_config roots) c -> safe_commit c.
Proof.
  intros Hadmissible [st ctrl] Hreach; pose proof (@reachable_control_safe tf roots _ Hadmissible Hreach) as Hsafe.
  destruct ctrl; try exact I; unfold safe_commit; cbn [R.cfg_state R.cfg_control].
  destruct (R.set_value (R.flush_deferred st) f t) as [next next_fr] eqn:E; cbn.
  apply (@set_value_phase_safe (R.flush_deferred st) f t next next_fr); [exact (Forall_inv Hsafe)|exact (Hadmissible _ Hreach)|exact E].
Qed.
Theorem successful_run_fixed_from_admissible_commits fuel tf roots final :
  Features.recompute_controlled = true -> Features.defer_spawns = true -> no_side_effects tf ->
  (forall c, Sem.steps tf (R.initial_config roots) c -> current_admissible c) ->
  R.solve_fuel fuel tf roots = Some final -> narrowing_fixed_with narrow (fun _ _ direct => direct) tf final.
Proof.
  intros Hon Hdefer Hpure Hadmissible; apply successful_run_fixed_from_safe_commits; try assumption;
    exact (@reachable_commit_safe tf roots Hadmissible).
Qed.
End PhasePropagation.

(** The phase frontier supplies admissibility globally. These laws are
    discharged by the OneBox instance rather than exposed as new premises in
    its public theorems. Recomputing controlled owners is needed only at the
    final fixedness step. *)
Section GlobalWaveFixedness.
Variable phase_narrow : U.phase -> Prop.
Hypothesis phase_initial_safe : forall owner, safe (U.initial_phase false owner).
Hypothesis phase_initial_wide : forall owner, ~ phase_narrow (U.initial_phase false owner).
Hypothesis phase_update_safe : forall owner phase old input, safe phase ->
  (phase_narrow phase -> D.leq input old = true) -> safe (fst (U.update false owner phase old input)).
Hypothesis phase_update_narrow : forall owner phase old input, safe phase ->
  phase_narrow (fst (U.update false owner phase old input)) -> D.leq input old = true.
Hypothesis phase_update_descends : forall owner phase old input, safe phase -> D.leq input old = true ->
  D.leq (snd (U.update false owner phase old input)) old = true.
Theorem ordinary_safe_commits tf roots c : Features.defer_spawns = true -> monotonic_system tf -> no_side_effects tf ->
  Sem.steps tf (R.initial_config roots) c -> safe_commit c.
Proof.
  intros Hdefer Hmono Hpure Hreach.
  pose proof (@ordinary_waves safe phase_narrow phase_initial_safe phase_initial_wide phase_update_safe
    phase_update_narrow phase_update_descends tf roots c Hdefer Hpure Hmono Hreach) as Hwave.
  destruct c as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k]; try exact I.
  unfold safe_commit; cbn [R.cfg_state R.cfg_control]; destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:E; cbn.
  destruct (Forall_inv Hwave) as [Hsafe Hfront].
  exact (@wave_set_safe safe phase_narrow phase_update_safe (R.flush_deferred st) fr direct next next_fr Hsafe
    (fun Hnarrow => @wave_commit_input tf roots st fr direct k Hdefer Hpure Hreach (Hfront Hnarrow)) E).
Qed.
Theorem successful_run_fixed fuel tf roots final : Features.recompute_controlled = true -> Features.defer_spawns = true ->
  monotonic_system tf -> no_side_effects tf -> R.solve_fuel fuel tf roots = Some final ->
  narrowing_fixed_with narrow (fun _ _ direct => direct) tf final.
Proof.
  intros Hon Hdefer Hmono Hpure Hrun; apply (@successful_run_fixed_from_safe_commits fuel tf roots final); try assumption.
  intros c Hreach; exact (@ordinary_safe_commits tf roots c Hdefer Hmono Hpure Hreach).
Qed.
End GlobalWaveFixedness.

End Narrowing.
End QuietFixedness.

(** Once episodes return with all higher work drained, the outer scheduler
    finishes by decreasing the queue ceiling and the finite FIFO credit. *)
Definition episode_completes tf start owner k := exists final,
  Sem.steps tf start (configuration final (R.Return k)) /\ queue_below final owner.
Definition outer_control remaining := match remaining with None => R.RunLoop | Some roots => R.RunSeedLoop roots end.
Definition outer_stack remaining := match remaining with None => R.KLoop | Some roots => R.KSeedLoop roots end.
Lemma reachable_queue_ceiling tf roots (finite : Sem.finite_system tf roots) c :
  Sem.steps tf (R.initial_config roots) c -> queue_under (S (length (Sem.support finite))) (R.cfg_state c).
Proof.
  intro Hreach; pose proof (shape_queue_ranks (inv_shape (proj2 (@reachable_invariants tf roots c Hreach)))) as Hranked.
  apply Forall_forall; intros owner Hin; destruct (proj1 (Forall_forall _ _) Hranked owner Hin) as [n Hn].
  unfold priority; rewrite Hn; pose proof (@reachable_rank_bound tf roots finite c owner n Hreach Hn); lia.
Qed.
Lemma terminal_path_fuel tf roots final : Sem.terminates_to tf roots final ->
  exists fuel, R.solve_fuel fuel tf roots = Some final.
Proof.
  intros [Hpath [Hq [Hw Hp]]]; destruct (path_run Hpath) as [fuel Hfuel]; exists fuel.
  unfold R.solve_fuel; rewrite Hfuel; unfold Sem.terminal_config,R.terminal_state; cbn; now rewrite Hq,Hw,Hp.
Qed.
Section OuterCompletion.
Variable tf : Syntax.system.
Variable roots : list V.t.
Variable finite : Sem.finite_system tf roots.
Hypothesis episodes_complete : forall st owner k,
  Sem.steps tf (R.initial_config roots) (configuration st (R.StartEpisode owner k)) ->
  episode_completes tf (configuration st (R.StartEpisode owner k)) owner k.
Lemma outer_resume st remaining : R.next_config tf (configuration st (R.Return (outer_stack remaining))) =
  Some (configuration st (outer_control remaining)).
Proof. destruct remaining; reflexivity. Qed.
Lemma outer_pop st remaining owner tail : R.queue st = owner :: tail ->
  R.next_config tf (configuration st (outer_control remaining)) =
    Some (configuration (R.with_queue st tail) (R.StartEpisode owner (outer_stack remaining))).
Proof. intro Hq; destruct remaining; unfold R.next_config; cbn [configuration R.cfg_state R.cfg_control outer_control outer_stack R.queue_pop]; now rewrite Hq. Qed.
Lemma outer_queue_finishes : forall ceiling st remaining,
  Sem.steps tf (R.initial_config roots) (configuration st (outer_control remaining)) -> queue_under ceiling st ->
  exists final, Sem.steps tf (configuration st (outer_control remaining)) (configuration final (outer_control remaining)) /\ R.queue final = [].
Proof.
  intro ceiling; induction ceiling using lt_wf_ind; intros st remaining Hreach Hceiling.
  destruct (R.queue st) as [|owner tail] eqn:Hqueue.
  - exists st; split; [constructor|exact Hqueue].
  - pose proof (@outer_pop st remaining owner tail Hqueue) as Hpop.
    assert (Hstart : Sem.steps tf (R.initial_config roots) (configuration (R.with_queue st tail) (R.StartEpisode owner (outer_stack remaining)))) by (eapply path_extend; eassumption).
    destruct (episodes_complete Hstart) as [returned [Hepisode Hbelow]].
    assert (Hreturn : Sem.steps tf (R.initial_config roots) (configuration returned (R.Return (outer_stack remaining)))) by (eapply path_join; eassumption).
    assert (Hresume : Sem.steps tf (R.initial_config roots) (configuration returned (outer_control remaining))) by (eapply path_extend; [exact Hreturn|apply outer_resume]).
    assert (Hrank : ranked (R.with_queue st tail) owner) by exact (Forall_inv (shape_stack_ranks (inv_shape (proj2 (@reachable_invariants tf roots _ Hstart))))).
    pose proof (@priority_extension (R.with_queue st tail) returned owner (@path_rank_extension tf _ _ Hepisode) Hrank) as Hpriority.
    change (priority st owner = priority returned owner) in Hpriority.
    assert (Hsmall : priority st owner < ceiling).
    { unfold queue_under in Hceiling; rewrite Hqueue in Hceiling; exact (Forall_inv Hceiling). }
    assert (Hnext : queue_under (priority st owner) returned) by (rewrite Hpriority; exact Hbelow).
    destruct (H (priority st owner) Hsmall returned remaining Hresume Hnext) as [final [Htail Hempty]].
    exists final; split; [|exact Hempty]; eapply Sem.StepsStep; [exact Hpop|].
    eapply path_join; [exact Hepisode|eapply Sem.StepsStep; [apply outer_resume|exact Htail]].
Qed.
Lemma seed_next st owner remaining : exists after,
  R.next_config tf (configuration st (R.RunSeeds (owner :: remaining))) = Some after /\
  (R.cfg_control after = R.RunSeeds remaining \/ R.cfg_control after = R.StartEpisode owner (R.KSeedLoop remaining)).
Proof.
  unfold R.next_config; cbn [configuration R.cfg_state R.cfg_control];
    destruct (R.is_materialized st owner || R.is_dormant st owner);
    [|destruct (Ranks.lookup (R.ranking st) owner); [|destruct (R.pure_bottom_rhs tf owner)]].
  all: eexists; split; [reflexivity|]; cbn; auto.
Qed.
Lemma seed_episode_finishes st owner remaining :
  Sem.steps tf (R.initial_config roots) (configuration st (R.StartEpisode owner (R.KSeedLoop remaining))) ->
  exists final, Sem.steps tf (configuration st (R.StartEpisode owner (R.KSeedLoop remaining))) (configuration final (R.RunSeeds remaining)).
Proof.
  intro Hreach; destruct (episodes_complete Hreach) as [returned [Hepisode _]].
  assert (Hreturned : Sem.steps tf (R.initial_config roots) (configuration returned (R.RunSeedLoop remaining))).
  { eapply path_extend; [eapply path_join; eassumption|reflexivity]. }
  destruct (@outer_queue_finishes (S (length (Sem.support finite))) returned (Some remaining) Hreturned
    (@reachable_queue_ceiling tf roots finite _ Hreturned)) as [drained [Hdrain Hempty]].
  exists drained; eapply path_join; [exact Hepisode|eapply Sem.StepsStep; [reflexivity|]].
  eapply path_join; [exact Hdrain|apply Sem.StepsStep with (configuration drained (R.RunSeeds remaining)); [|constructor]].
  unfold Sem.step,R.next_config; cbn [configuration R.cfg_state R.cfg_control]; rewrite Hempty; reflexivity.
Qed.
Lemma seeds_finish remaining : forall st,
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunSeeds remaining)) ->
  exists final, Sem.steps tf (configuration st (R.RunSeeds remaining)) (configuration final R.RunLoop).
Proof.
  induction remaining as [|owner rest IH]; intros st Hreach.
  - exists st; apply Sem.StepsStep with (configuration st R.RunLoop); [reflexivity|constructor].
  - destruct (@seed_next st owner rest) as [[next ctrl] [E [Hctrl|Hctrl]]]; cbn [R.cfg_control] in Hctrl; subst ctrl;
      assert (Hnext : Sem.steps tf (R.initial_config roots) (configuration next _)) by (eapply path_extend; eassumption).
    + destruct (IH next Hnext) as [final Htail]; exists final; eapply Sem.StepsStep; eassumption.
    + destruct (@seed_episode_finishes next owner rest Hnext) as [returned Hepisode].
      destruct (IH returned (@path_join tf _ _ _ Hnext Hepisode)) as [final Htail].
      exists final; eapply Sem.StepsStep; [exact E|eapply path_join; eassumption].
Qed.
Lemma loop_finishes : forall budget st,
  Sem.steps tf (R.initial_config roots) (configuration st R.RunLoop) ->
  spawn_credit (Sem.support finite) st <= budget ->
  exists final, Sem.steps tf (configuration st R.RunLoop) (configuration final R.RunLoop) /\
    R.queue final = [] /\ R.pending_spawns final = [].
Proof.
  intro budget; induction budget using lt_wf_ind; intros st Hreach Hbudget.
  destruct (@outer_queue_finishes (S (length (Sem.support finite))) st None Hreach
    (@reachable_queue_ceiling tf roots finite _ Hreach)) as [drained [Hdrain Hempty]].
  assert (Hdrained : Sem.steps tf (R.initial_config roots) (configuration drained R.RunLoop)) by (eapply path_join; eassumption).
  pose proof (@spawn_credit_path tf roots finite _ _ Hreach Hdrain) as Hdrain_credit.
  destruct (R.pending_spawns drained) as [|target rest] eqn:Hfifo.
  - exists drained; split; [exact Hdrain|auto].
  - set (next := R.with_spawns drained rest (R.requested_spawns drained)).
    assert (Hpop : Sem.step tf (configuration drained R.RunLoop) (configuration next (R.RunSeeds [target]))).
    { unfold Sem.step,R.next_config; cbn [configuration R.cfg_state R.cfg_control R.queue_pop]; now rewrite Hempty,Hfifo. }
    assert (Hnext : Sem.steps tf (R.initial_config roots) (configuration next (R.RunSeeds [target]))) by (eapply path_extend; eassumption).
    destruct (@seeds_finish [target] next Hnext) as [returned Hseeds].
    pose proof (@spawn_credit_path tf roots finite _ _ Hnext Hseeds) as Hseed_credit.
    pose proof (@spawn_credit_pop (Sem.support finite) drained target rest Hfifo) as Hpop_credit.
    assert (Hsmall : spawn_credit (Sem.support finite) returned < budget).
    { change (spawn_credit (Sem.support finite) returned <= spawn_credit (Sem.support finite) next) in Hseed_credit.
      change (spawn_credit (Sem.support finite) drained <= spawn_credit (Sem.support finite) st) in Hdrain_credit; unfold next in *; lia. }
    destruct (H (spawn_credit (Sem.support finite) returned) Hsmall returned
      (@path_join tf _ _ _ Hnext Hseeds) (Nat.le_refl _)) as [final [Htail Hquiet]].
    exists final; split; [|exact Hquiet]; eapply path_join; [exact Hdrain|eapply Sem.StepsStep; [exact Hpop|eapply path_join; eassumption]].
Qed.
Theorem finish_from_episodes : exists final, Sem.terminates_to tf roots final.
Proof.
  destruct (@seeds_finish roots R.empty_state (@Sem.StepsRefl tf _)) as [loop Hseeds].
  destruct (@loop_finishes (spawn_credit (Sem.support finite) loop) loop Hseeds (Nat.le_refl _)) as [final [Hloop [Hqueue Hfifo]]].
  assert (Hreach : Sem.steps tf (R.initial_config roots) (configuration final R.RunLoop)) by (eapply path_join; eassumption).
  exists final; split; [exact Hreach|split; [exact Hqueue|split; [|exact Hfifo]]].
  exact (shape_wakes (inv_shape (proj2 (@reachable_invariants tf roots _ Hreach)))).
Qed.
Corollary fuel_from_episodes : exists fuel final, R.solve_fuel fuel tf roots = Some final.
Proof. destruct finish_from_episodes as [final Hfinish]; destruct (terminal_path_fuel Hfinish) as [fuel Hfuel]; eauto. Qed.
End OuterCompletion.

(** Structural evaluation consumes a transfer tree. Calls to higher owners
    may be supplied by the outer rank induction; their return continuations
    preserve the evaluating owner's identity. *)
Lemma sorted_head_strict st head tail x : sorted_queue st (head :: tail) -> In x tail -> priority st x < priority st head.
Proof. intros H Hin; inversion H; subst; exact (proj1 (Forall_forall _ _) H3 x Hin). Qed.
Definition higher_completion tf roots owner := forall st child k,
  Sem.steps tf (R.initial_config roots) (configuration st (R.StartEpisode child k)) ->
  R.rank_lt st owner child = true -> episode_completes tf (configuration st (R.StartEpisode child k)) child k.
Lemma suspended_higher_complete tf roots owner st child k : higher_completion tf roots owner ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.StartEpisode child k)) -> In owner (suspended_owners k) ->
  episode_completes tf (configuration st (R.StartEpisode child k)) child k.
Proof.
  intros Hhigher Hreach Hin; apply Hhigher; [exact Hreach|].
  pose proof (inv_shape (proj2 (@reachable_invariants tf roots _ Hreach))) as Hshape.
  pose proof (shape_stack_ranks Hshape) as Hranked; change (ranked_list st (child :: suspended_owners k)) in Hranked.
  apply (proj2 (@compare_rank st owner child (proj1 (Forall_forall _ _) Hranked owner ltac:(cbn; now right)) (Forall_inv Hranked))).
  exact (@sorted_head_strict st child (suspended_owners k) owner (shape_stack_order Hshape) Hin).
Qed.
Lemma get_next_shape tf st fr target tail k : exists after,
  R.next_config tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) = Some after /\
  ((exists next_fr value, R.cfg_control after = R.RunRhs next_fr (tail value) k /\ R.frame_owner next_fr = R.frame_owner fr) \/
   R.cfg_control after = R.StartEpisode target (R.KAfterGet fr target tail k)).
Proof.
  unfold R.next_config; cbn [configuration R.cfg_state R.cfg_control Syntax.Get];
    destruct (R.is_dormant st target); [|destruct (Ranks.lookup (R.ranking st) target);
      [|destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target))]].
  all: repeat match goal with |- context [if ?test then _ else _] => destruct test eqn:? end.
  all: repeat match goal with
    |- context [R.complete_get ?base ?frame ?read] =>
      let E := fresh "Eget" in destruct (R.complete_get base frame read) as [[? ?] ?] eqn:E;
      let H := fresh "Howner" in pose proof (proj1 (@get_phase_owner base frame read _ _ _ E)) as H
  | |- context [R.dirty_complete_get ?sys ?base ?frame ?read] =>
      let E := fresh "Eget" in destruct (R.dirty_complete_get sys base frame read) as [[? ?] ?] eqn:E;
      let H := fresh "Howner" in pose proof (proj1 (@dirty_get_phase_owner sys base frame read _ _ _ E)) as H
  end.
  all: eexists; split; [reflexivity|]; cbn; first [right; reflexivity|left; eexists _,_; split; [reflexivity|auto]].
Qed.
Lemma get_evaluation_progress tf roots st fr target tail k : higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  exists next next_fr value,
    Sem.steps tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) (configuration next (R.RunRhs next_fr (tail value) k)) /\
    R.frame_owner next_fr = R.frame_owner fr.
Proof.
  intros Hhigher Hreach; destruct (@get_next_shape tf st fr target tail k) as [[next ctrl] [E [Hdirect|Hchild]]]; cbn [R.cfg_control] in *.
  - destruct Hdirect as [next_fr [value [Hctrl Howner]]]; subst ctrl; exists next,next_fr,value; split; [eapply Sem.StepsStep; [exact E|constructor]|exact Howner].
  - subst ctrl; assert (Hnext : Sem.steps tf (R.initial_config roots) (configuration next (R.StartEpisode target (R.KAfterGet fr target tail k)))) by (eapply path_extend; eassumption).
    destruct (@suspended_higher_complete tf roots (R.frame_owner fr) next target (R.KAfterGet fr target tail k) Hhigher Hnext ltac:(cbn; now left)) as [returned [Hepisode _]].
    destruct (R.complete_get returned fr target) as [[resumed resumed_fr] value] eqn:Eget; exists resumed,resumed_fr,value; split.
    + eapply Sem.StepsStep; [exact E|eapply path_join; [exact Hepisode|eapply Sem.StepsStep; [|constructor]]].
      unfold Sem.step,R.next_config; cbn [configuration R.cfg_state R.cfg_control]; now rewrite Eget.
    + exact (proj1 (@get_phase_owner returned fr target resumed resumed_fr value Eget)).
Qed.

Ltac decompose_operation :=
  repeat first [match goal with |- context [R.write_side_contribution ?st ?fr ?target ?value] =>
      destruct (R.write_side_contribution st fr target value) as [? ?] eqn:? end
    | match goal with |- context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end
    | match goal with |- context [if ?test then _ else _] => destruct test eqn:? end].
Lemma spawn_next_shape tf st fr target tail k : exists after,
  R.next_config tf (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) = Some after /\
  (R.cfg_control after = R.RunRhs fr tail k \/ R.cfg_control after = R.StartEpisode target (R.KAfterSpawn fr tail k)).
Proof.
  unfold R.next_config; cbn [configuration R.cfg_state R.cfg_control Syntax.Spawn]; decompose_operation.
  all: eexists; split; [reflexivity|]; cbn; auto.
Qed.
Lemma spawn_evaluation_progress tf roots st fr target tail k : higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  exists next, Sem.steps tf (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) (configuration next (R.RunRhs fr tail k)).
Proof.
  intros Hhigher Hreach; destruct (@spawn_next_shape tf st fr target tail k) as [[next ctrl] [E [Hdirect|Hchild]]]; cbn [R.cfg_control] in *.
  - subst ctrl; exists next; eapply Sem.StepsStep; [exact E|constructor].
  - subst ctrl; assert (Hnext : Sem.steps tf (R.initial_config roots) (configuration next (R.StartEpisode target (R.KAfterSpawn fr tail k)))) by (eapply path_extend; eassumption).
    destruct (@suspended_higher_complete tf roots (R.frame_owner fr) next target (R.KAfterSpawn fr tail k) Hhigher Hnext ltac:(cbn; now left)) as [returned [Hepisode _]].
    exists returned; eapply Sem.StepsStep; [exact E|eapply path_join; [exact Hepisode|eapply Sem.StepsStep; [reflexivity|constructor]]].
Qed.
Lemma side_next_shape tf st fr target raw tail k : exists after,
  R.next_config tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) = Some after /\
  ((exists next_fr, R.cfg_control after = R.RunRhs next_fr tail k /\ R.frame_owner next_fr = R.frame_owner fr) \/
   exists next_fr, R.cfg_control after = R.StartEpisode target (R.KAfterSide next_fr tail k) /\ R.frame_owner next_fr = R.frame_owner fr).
Proof.
  unfold R.next_config; cbn [configuration R.cfg_state R.cfg_control Syntax.Side]; decompose_operation;
    cbn [R.record_side_input]; unfold R.continue_side; decompose_operation.
  all: eexists; split; [reflexivity|]; cbn;
    first [left; eexists; split; reflexivity|right; eexists; split; reflexivity].
Qed.
Lemma side_evaluation_progress tf roots st fr target raw tail k : higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) ->
  exists next next_fr,
    Sem.steps tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) (configuration next (R.RunRhs next_fr tail k)) /\
    R.frame_owner next_fr = R.frame_owner fr.
Proof.
  intros Hhigher Hreach; destruct (@side_next_shape tf st fr target raw tail k) as [[next ctrl] [E [Hdirect|Hchild]]]; cbn [R.cfg_control] in *.
  - destruct Hdirect as [next_fr [Hctrl Howner]]; subst ctrl; exists next,next_fr; split; [eapply Sem.StepsStep; [exact E|constructor]|exact Howner].
  - destruct Hchild as [next_fr [Hctrl Howner]]; subst ctrl;
      assert (Hnext : Sem.steps tf (R.initial_config roots) (configuration next (R.StartEpisode target (R.KAfterSide next_fr tail k)))) by (eapply path_extend; eassumption).
    destruct (@suspended_higher_complete tf roots (R.frame_owner fr) next target (R.KAfterSide next_fr tail k) Hhigher Hnext
      ltac:(cbn; left; exact Howner)) as [returned [Hepisode _]].
    exists returned,next_fr; split; [|exact Howner].
    eapply Sem.StepsStep; [exact E|eapply path_join; [exact Hepisode|eapply Sem.StepsStep; [reflexivity|constructor]]].
Qed.
Lemma dead_next_shape tf st fr direct target rest k : exists after,
  R.next_config tf (configuration st (R.RunDead fr direct (target :: rest) k)) = Some after /\
  (R.cfg_control after = R.RunDead fr direct rest k \/ R.cfg_control after = R.StartEpisode target (R.KDead fr direct rest k)).
Proof.
  unfold R.next_config; cbn [configuration R.cfg_state R.cfg_control]; decompose_operation;
    unfold R.continue_dead; decompose_operation.
  all: eexists; split; [reflexivity|]; cbn; auto.
Qed.
Lemma dead_evaluation_progress tf roots st fr direct target rest k : higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunDead fr direct (target :: rest) k)) ->
  exists next, Sem.steps tf (configuration st (R.RunDead fr direct (target :: rest) k)) (configuration next (R.RunDead fr direct rest k)).
Proof.
  intros Hhigher Hreach; destruct (@dead_next_shape tf st fr direct target rest k) as [[next ctrl] [E [Hdirect|Hchild]]]; cbn [R.cfg_control] in *.
  - subst ctrl; exists next; eapply Sem.StepsStep; [exact E|constructor].
  - subst ctrl; assert (Hnext : Sem.steps tf (R.initial_config roots) (configuration next (R.StartEpisode target (R.KDead fr direct rest k)))) by (eapply path_extend; eassumption).
    destruct (@suspended_higher_complete tf roots (R.frame_owner fr) next target (R.KDead fr direct rest k) Hhigher Hnext ltac:(cbn; now left)) as [returned [Hepisode _]].
    exists returned; eapply Sem.StepsStep; [exact E|eapply path_join; [exact Hepisode|eapply Sem.StepsStep; [reflexivity|constructor]]].
Qed.
Lemma dead_evaluation_finishes tf roots pending : forall st fr direct k,
  higher_completion tf roots (R.frame_owner fr) -> Sem.steps tf (R.initial_config roots) (configuration st (R.RunDead fr direct pending k)) ->
  exists next, Sem.steps tf (configuration st (R.RunDead fr direct pending k)) (configuration next (R.RunCommit fr direct k)).
Proof.
  induction pending as [|target rest IH]; intros st fr direct k Hhigher Hreach.
  - exists (R.publish_targets st fr); eapply Sem.StepsStep; [reflexivity|constructor].
  - destruct (@dead_evaluation_progress tf roots st fr direct target rest k Hhigher Hreach) as [next Hprogress].
    destruct (IH next fr direct k Hhigher (@path_join tf _ _ _ Hreach Hprogress)) as [final Htail].
    exists final; eapply path_join; eassumption.
Qed.
Lemma return_reaches_commit tf roots st fr direct k : higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr (Syntax.Ret direct) k)) ->
  exists next, Sem.steps tf (configuration st (R.RunRhs fr (Syntax.Ret direct) k)) (configuration next (R.RunCommit fr direct k)).
Proof.
  intros Hhigher Hreach; set (pending := if Features.eliminate_dead_sides then S.elements (R.frame_previous_targets fr) else []).
  assert (E : Sem.step tf (configuration st (R.RunRhs fr (Syntax.Ret direct) k))
    (configuration st (R.RunDead fr direct pending k))) by reflexivity.
  destruct (@dead_evaluation_finishes tf roots pending st fr direct k Hhigher
    (@path_extend tf _ _ _ Hreach E)) as [final Htail]; exists final; eapply Sem.StepsStep; eassumption.
Qed.
Theorem rhs_evaluation_finishes tf roots body : forall st fr k,
  higher_completion tf roots (R.frame_owner fr) -> Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr body k)) ->
  exists next next_fr direct, Sem.steps tf (configuration st (R.RunRhs fr body k)) (configuration next (R.RunCommit next_fr direct k)) /\
    R.frame_owner next_fr = R.frame_owner fr.
Proof.
  induction body as [direct|target tail IH|target raw tail IH|target tail IH]; intros st fr k Hhigher Hreach.
  - destruct (@return_reaches_commit tf roots st fr direct k Hhigher Hreach) as [next Hdone]; exists next,fr,direct; auto.
  - destruct (@get_evaluation_progress tf roots st fr target tail k Hhigher Hreach) as [next [next_fr [value [Hprogress Howner]]]].
    destruct (IH value next next_fr k ltac:(now rewrite Howner) (@path_join tf _ _ _ Hreach Hprogress)) as [final [final_fr [direct [Htail Hfinal]]]].
    exists final,final_fr,direct; split; [eapply path_join; eassumption|congruence].
  - destruct (@side_evaluation_progress tf roots st fr target raw tail k Hhigher Hreach) as [next [next_fr [Hprogress Howner]]].
    destruct (IH next next_fr k ltac:(now rewrite Howner) (@path_join tf _ _ _ Hreach Hprogress)) as [final [final_fr [direct [Htail Hfinal]]]].
    exists final,final_fr,direct; split; [eapply path_join; eassumption|congruence].
  - destruct (@spawn_evaluation_progress tf roots st fr target tail k Hhigher Hreach) as [next Hprogress].
    destruct (IH next fr k Hhigher (@path_join tf _ _ _ Hreach Hprogress)) as [final [final_fr [direct [Htail Hfinal]]]].
    exists final,final_fr,direct; split; [eapply path_join; eassumption|exact Hfinal].
Qed.

Definition drain_boundary tf owner k c := queue_below (R.cfg_state c) owner /\
  R.deferred_wakes (R.cfg_state c) = [] /\
  (R.cfg_control c = R.Return k \/ exists fr, R.cfg_control c = R.RunRhs fr (tf owner) k /\ R.frame_owner fr = owner).
Lemma drain_evaluation_finishes tf roots : forall ceiling st fr k,
  higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunDrain fr k)) -> queue_under ceiling st ->
  exists after, Sem.steps tf (configuration st (R.RunDrain fr k)) after /\ drain_boundary tf (R.frame_owner fr) k after.
Proof.
  intro ceiling; induction ceiling using lt_wf_ind; intros st fr k Hhigher Hreach Hceiling.
  pose proof (proj2 (@reachable_invariants tf roots _ Hreach)) as Hinv.
  destruct (R.queue st) as [|head tail] eqn:Hqueue.
  - set (after := configuration (R.reset_registered_cells st (R.frame_owner fr)) (R.Return k)).
    assert (E : Sem.step tf (configuration st (R.RunDrain fr k)) after).
    { unfold Sem.step,R.next_config,after; cbn [configuration R.cfg_state R.cfg_control R.queue_peek]; now rewrite Hqueue. }
    exists after; split; [eapply Sem.StepsStep; [exact E|constructor]|split; [|split; [|now left]]].
    2: { change (R.deferred_wakes (R.reset_registered_cells st (R.frame_owner fr)) = []);
      unfold R.reset_registered_cells; destruct Features.restart_side_phases;
        exact (shape_wakes (inv_shape Hinv)). }
    change (queue_below (R.reset_registered_cells st (R.frame_owner fr)) (R.frame_owner fr)).
    unfold queue_below,queue_under; rewrite reset_queue,Hqueue; constructor.
  - destruct (V.eq_dec head (R.frame_owner fr)) as [Hself|Hother].
    + subst head; set (prepared := R.clear_side_dirty (R.with_queue st tail) (R.frame_owner fr)).
      set (next_fr := R.fresh_frame prepared (R.frame_owner fr) (R.frame_phase fr)).
      set (after := configuration prepared (R.RunRhs next_fr (tf (R.frame_owner fr)) k)).
      assert (E : Sem.step tf (configuration st (R.RunDrain fr k)) after).
      { unfold Sem.step,R.next_config,after; cbn [configuration R.cfg_state R.cfg_control R.queue_peek R.queue_pop]; rewrite Hqueue; cbn;
          destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr)); [reflexivity|contradiction]. }
      exists after; split; [eapply Sem.StepsStep; [exact E|constructor]|split; [|split; [|right; exists next_fr; auto]]].
      2: { change (R.deferred_wakes st = []); exact (shape_wakes (inv_shape Hinv)). }
      change (queue_below prepared (R.frame_owner fr)); eapply queue_below_fields with (st := R.with_queue st tail);
        [reflexivity|reflexivity|apply popped_below].
      pose proof (shape_queue_order (inv_shape Hinv)) as Hsorted; change (sorted_queue st (R.queue st)) in Hsorted; now rewrite Hqueue in Hsorted.
    + destruct (R.rank_lt st (R.frame_owner fr) head) eqn:Hhigher_head.
      * assert (E : Sem.step tf (configuration st (R.RunDrain fr k))
          (configuration (R.with_queue st tail) (R.StartEpisode head (R.KDrain fr k)))).
        { unfold Sem.step,R.next_config; cbn [configuration R.cfg_state R.cfg_control R.queue_peek R.queue_pop]; rewrite Hqueue; cbn;
            destruct (V.eq_dec head (R.frame_owner fr)); [contradiction|now rewrite Hhigher_head]. }
        assert (Hstart : Sem.steps tf (R.initial_config roots) (configuration (R.with_queue st tail) (R.StartEpisode head (R.KDrain fr k)))) by (eapply path_extend; eassumption).
        destruct (@suspended_higher_complete tf roots (R.frame_owner fr) (R.with_queue st tail) head (R.KDrain fr k) Hhigher Hstart ltac:(cbn; now left)) as [returned [Hepisode Hbelow]].
        assert (Hreturn : Sem.steps tf (R.initial_config roots) (configuration returned (R.Return (R.KDrain fr k)))) by (eapply path_join; eassumption).
        assert (Hresume : Sem.steps tf (R.initial_config roots) (configuration returned (R.RunDrain fr k))) by (eapply path_extend; [exact Hreturn|reflexivity]).
        pose proof (shape_queue_ranks (inv_shape Hinv)) as Hranked; change (ranked_list st (R.queue st)) in Hranked; rewrite Hqueue in Hranked.
        pose proof (@priority_extension (R.with_queue st tail) returned head (@path_rank_extension tf _ _ Hepisode) (Forall_inv Hranked)) as Hpriority;
          change (priority st head = priority returned head) in Hpriority.
        assert (Hsmall : priority st head < ceiling) by (unfold queue_under in Hceiling; rewrite Hqueue in Hceiling; exact (Forall_inv Hceiling)).
        assert (Hnext_ceiling : queue_under (priority st head) returned) by (rewrite Hpriority; exact Hbelow).
        destruct (H (priority st head) Hsmall returned fr k Hhigher Hresume Hnext_ceiling) as [after [Htail Hboundary]].
        exists after; split; [|exact Hboundary]; eapply Sem.StepsStep; [exact E|eapply path_join; [exact Hepisode|eapply Sem.StepsStep; [reflexivity|exact Htail]]].
      * set (after := configuration (R.reset_registered_cells st (R.frame_owner fr)) (R.Return k)).
        assert (E : Sem.step tf (configuration st (R.RunDrain fr k)) after).
        { unfold Sem.step,R.next_config,after; cbn [configuration R.cfg_state R.cfg_control R.queue_peek R.queue_pop]; rewrite Hqueue; cbn;
            destruct (V.eq_dec head (R.frame_owner fr)); [contradiction|now rewrite Hhigher_head]. }
        exists after; split; [eapply Sem.StepsStep; [exact E|constructor]|split; [|split; [|now left]]].
        2: { change (R.deferred_wakes (R.reset_registered_cells st (R.frame_owner fr)) = []);
          unfold R.reset_registered_cells; destruct Features.restart_side_phases;
            exact (shape_wakes (inv_shape Hinv)). }
        pose proof (@closing_queue_under tf roots st fr k after Hinv E eq_refl) as Hbelow.
        unfold queue_below,priority; cbn [after configuration R.cfg_state]; rewrite reset_ranking; exact Hbelow.
Qed.

Corollary rhs_round_boundary tf roots (finite : Sem.finite_system tf roots) st fr body k :
  higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr body k)) ->
  exists after, Sem.steps tf (configuration st (R.RunRhs fr body k)) after /\ drain_boundary tf (R.frame_owner fr) k after.
Proof.
  intros Hhigher Hreach; destruct (@rhs_evaluation_finishes tf roots body st fr k Hhigher Hreach) as [committed [commit_fr [direct [Hevaluation Howner]]]].
  assert (Hcommit : Sem.steps tf (R.initial_config roots) (configuration committed (R.RunCommit commit_fr direct k))) by (eapply path_join; eassumption).
  destruct (R.set_value (R.flush_deferred committed) commit_fr direct) as [next next_fr] eqn:Eset.
  assert (E : Sem.step tf (configuration committed (R.RunCommit commit_fr direct k)) (configuration next (R.RunDrain next_fr k))).
  { unfold Sem.step,R.next_config; cbn [configuration R.cfg_state R.cfg_control]; now rewrite Eset. }
  assert (Hnext : Sem.steps tf (R.initial_config roots) (configuration next (R.RunDrain next_fr k))) by (eapply path_extend; eassumption).
  assert (Hnext_owner : R.frame_owner next_fr = R.frame_owner fr) by (rewrite (@set_value_owner _ _ _ _ _ Eset); exact Howner).
  destruct (@drain_evaluation_finishes tf roots (S (length (Sem.support finite))) next next_fr k
    ltac:(now rewrite Hnext_owner) Hnext (@reachable_queue_ceiling tf roots finite _ Hnext)) as [after [Hdrain Hboundary]].
  exists after; split; [eapply path_join; [exact Hevaluation|eapply Sem.StepsStep; eassumption]|now rewrite Hnext_owner in Hboundary].
Qed.
Lemma paths_comparable tf first left right : Sem.steps tf first left -> Sem.steps tf first right ->
  Sem.steps tf left right \/ Sem.steps tf right left.
Proof.
  intros Hleft; revert right; induction Hleft; intros right Hright; [left; exact Hright|].
  inversion Hright as [|start next final E Htail]; subst; [right; eapply Sem.StepsStep; eassumption|].
  assert (Echildren : b = next) by (unfold Sem.step in *; congruence); subst next; apply IHHleft; exact Htail.
Qed.
Lemma reachable_priority_agrees tf roots left right owner : Sem.steps tf (R.initial_config roots) left ->
  Sem.steps tf (R.initial_config roots) right -> ranked (R.cfg_state left) owner -> ranked (R.cfg_state right) owner ->
  priority (R.cfg_state left) owner = priority (R.cfg_state right) owner.
Proof.
  intros Hleft Hright Hrank_left Hrank_right; destruct (@paths_comparable tf _ left right Hleft Hright) as [Hpath|Hpath].
  - exact (@priority_extension _ _ owner (@path_rank_extension tf _ _ Hpath) Hrank_left).
  - symmetry; exact (@priority_extension _ _ owner (@path_rank_extension tf _ _ Hpath) Hrank_right).
Qed.

(** Finite episodes use one shared machine. Side storage and promotion views
    isolate administrative transitions from the updates that spend credits. *)
Definition cell_view before after := R.side_cells after = R.side_cells before /\ R.contributions after = R.contributions before.
Lemma cell_view_refl st : cell_view st st.
Proof. split; reflexivity. Qed.
Lemma cell_view_trans first middle last : cell_view first middle -> cell_view middle last -> cell_view first last.
Proof. intros [Hc Hv] [Hc' Hv']; split; congruence. Qed.
Lemma cell_view_materialize st target : cell_view st (R.materialize st target).
Proof. unfold R.materialize; destruct (M.lookup _ _); split; reflexivity. Qed.
Lemma cell_view_observe st target : cell_view st (R.observe st target).
Proof. unfold R.observe; destruct (Ranks.observe _ _); split; reflexivity. Qed.
Lemma cell_view_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) -> cell_view st next.
Proof.
  unfold R.complete_get; intro E; inversion E; subst; eapply cell_view_trans; [|apply cell_view_materialize].
  destruct (R.rank_lt st (R.frame_owner fr) target); split; reflexivity.
Qed.
Lemma cell_view_dirty_finish st target value : cell_view st (dirty_finish st target value).
Proof. destruct value; split; reflexivity. Qed.
Lemma cell_view_dirty_get tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) -> cell_view st next.
Proof.
  unfold R.dirty_complete_get; set (prepared := R.materialize (if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) target).
  assert (Hprepared : cell_view st prepared).
  { unfold prepared; eapply cell_view_trans; [|apply cell_view_materialize]; destruct (R.rank_lt st (R.frame_owner fr) target); split; reflexivity. }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:Eread; intro E; inversion E; subst; [|exact Hprepared].
  destruct (@dirty_read_result tf prepared (R.frame_owner fr) target s Eread) as [direct [result [_ [_ [-> _]]]]].
  eapply cell_view_trans; [exact Hprepared|apply cell_view_dirty_finish].
Qed.
Lemma cell_view_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) -> cell_view st next.
Proof.
  intro E; apply set_value_cases in E as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; split; reflexivity.
Qed.
Definition controlled_extension before after := forall owner, S.mem owner (R.controlled before) = true -> S.mem owner (R.controlled after) = true.
Lemma controlled_extension_refl st : controlled_extension st st.
Proof. intros owner H; exact H. Qed.
Lemma controlled_extension_trans first middle last : controlled_extension first middle -> controlled_extension middle last -> controlled_extension first last.
Proof. intros H H' owner Hin; auto. Qed.
Lemma controlled_extension_fields before after : R.controlled after = R.controlled before -> controlled_extension before after.
Proof. intros E owner Hin; now rewrite E. Qed.
Lemma controlled_extension_promote st target : controlled_extension st (R.promote_controlled st target).
Proof. intros owner Hin; apply SL.add_spec; now right. Qed.
Lemma controlled_extension_materialize st target : controlled_extension st (R.materialize st target).
Proof. unfold R.materialize; destruct (M.lookup _ _); apply controlled_extension_fields; reflexivity. Qed.
Lemma controlled_extension_observe st target : controlled_extension st (R.observe st target).
Proof. unfold R.observe; destruct (Ranks.observe _ _); apply controlled_extension_fields; reflexivity. Qed.
Lemma controlled_extension_get st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) -> controlled_extension st next.
Proof.
  unfold R.complete_get; intro E; inversion E; subst; eapply controlled_extension_trans; [|apply controlled_extension_materialize].
  destruct (R.rank_lt st (R.frame_owner fr) target); [apply controlled_extension_fields; reflexivity|intros owner Hin; apply SL.add_spec; now right].
Qed.
Lemma controlled_extension_dirty_get tf st fr target next next_fr value : R.dirty_complete_get tf st fr target = (next,next_fr,value) -> controlled_extension st next.
Proof.
  unfold R.dirty_complete_get; set (prepared := R.materialize (if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) target).
  assert (Hp : controlled_extension st prepared).
  { unfold prepared; eapply controlled_extension_trans; [|apply controlled_extension_materialize];
      destruct (R.rank_lt st (R.frame_owner fr) target); [apply controlled_extension_refl|apply controlled_extension_promote]. }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:Eread; intro E; inversion E; subst; [|exact Hp].
  destruct (@dirty_read_result tf prepared (R.frame_owner fr) target s Eread) as [direct [result [_ [_ [-> _]]]]].
  eapply controlled_extension_trans; [exact Hp|destruct result; intros owner Hin; apply SL.add_spec; now right].
Qed.
Lemma controlled_extension_write st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) -> controlled_extension st next.
Proof.
  unfold R.write_side_contribution; intro E; inversion E; subst.
  unfold R.promote_side_target; destruct (R.rank_lt st target (R.frame_owner fr));
    [apply controlled_extension_fields; reflexivity|apply controlled_extension_promote].
Qed.
Lemma controlled_extension_commit st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) -> controlled_extension st next.
Proof.
  intro E; apply set_value_cases in E as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; apply controlled_extension_fields; reflexivity.
Qed.
Ltac controlled_membership :=
  cbn [R.controlled R.cfg_state R.with_queue R.with_dirty_side_targets R.with_deferred_wakes R.with_spawns
    R.with_readers R.with_dormant_bottom R.with_sigma R.with_ranking R.with_cells_and_resets R.with_last_targets];
  first [assumption|
    match goal with E : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- S.mem ?owner (R.controlled ?next) = true =>
      apply (@controlled_extension_get base fr target next next_fr value E owner); controlled_membership end|
    match goal with E : R.dirty_complete_get ?tf ?base ?fr ?target = (?next,?next_fr,?value) |- S.mem ?owner (R.controlled ?next) = true =>
      apply (@controlled_extension_dirty_get tf base fr target next next_fr value E owner); controlled_membership end|
    match goal with E : R.write_side_contribution ?base ?fr ?target ?input = (?next,?changed) |- S.mem ?owner (R.controlled ?next) = true =>
      apply (@controlled_extension_write base fr target input next changed E owner); controlled_membership end|
    match goal with E : R.set_value ?base ?fr ?input = (?next,?next_fr) |- S.mem ?owner (R.controlled ?next) = true =>
      apply (@controlled_extension_commit base fr input next next_fr E owner); controlled_membership end|
    match goal with |- context [R.observe ?base ?target] => unfold R.observe; destruct (Ranks.observe (R.ranking base) target); controlled_membership end|
    match goal with |- context [R.materialize ?base ?target] => unfold R.materialize; destruct (M.lookup (R.sigma base) target); controlled_membership end|
    progress unfold R.reset_registered_cells; destruct Features.restart_side_phases; controlled_membership|
    match goal with |- context [R.request_spawn ?base ?target] => unfold R.request_spawn; destruct (S.mem target (R.requested_spawns base)); controlled_membership end|
    progress unfold R.enqueue,R.mark_side_dirty,R.clear_side_dirty,R.remember_dormant,R.add_reader;
      controlled_membership|
    match goal with |- context [if ?test then _ else _] => destruct test eqn:?; controlled_membership end].
Ltac controlled_administration :=
  unfold controlled_extension; intros observed Hmember; controlled_membership.
Theorem step_controlled_extension tf before after : Sem.step tf before after -> controlled_extension (R.cfg_state before) (R.cfg_state after).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    unfold Sem.step,R.next_config; cbn [R.cfg_state R.cfg_control]; intro E.
  - inspect_machine_step E; try discriminate; inversion E; subst; controlled_administration.
  - destruct seeds; inspect_machine_step E; try discriminate; inversion E; subst; controlled_administration.
  - inspect_machine_step E; try discriminate; inversion E; subst; controlled_administration.
  - inversion E; subst; eapply controlled_extension_trans; [apply controlled_extension_materialize|apply controlled_extension_fields; reflexivity].
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      inspect_machine_step E; try discriminate; inversion E; subst; controlled_administration.
  - destruct pending; inspect_machine_step E; try discriminate; inversion E; subst; controlled_administration.
  - inspect_machine_step E; try discriminate; inversion E; subst; controlled_administration.
  - inspect_machine_step E; try discriminate; inversion E; subst; controlled_administration.
  - destruct k; inspect_machine_step E; try discriminate; inversion E; subst; controlled_administration.
Qed.
Theorem path_controlled_extension tf before after : Sem.steps tf before after -> controlled_extension (R.cfg_state before) (R.cfg_state after).
Proof. intro H; induction H; [apply controlled_extension_refl|eapply controlled_extension_trans; [exact (@step_controlled_extension tf a b H)|exact IHsteps]]. Qed.

(** Every storage mutation is either a side write or the close of an episode.
    Keeping this classification separate lets credit proofs share one case split. *)
Definition side_storage_effect (before after : R.config) := exists base fr target input next changed,
  cell_view (R.cfg_state before) base /\
  R.write_side_contribution base fr target input = (next,changed) /\
  cell_view next (R.cfg_state after) /\
  In (R.frame_owner fr) (active_owners (R.cfg_control before)).
Definition close_storage_effect (before after : R.config) := exists fr k,
  R.cfg_control before = R.RunDrain fr k /\ R.cfg_control after = R.Return k /\
  R.cfg_state after = R.reset_registered_cells (R.cfg_state before) (R.frame_owner fr).
Ltac cell_field_reduction :=
  cbn [R.cfg_state R.side_cells R.contributions R.with_queue R.with_dirty_side_targets R.with_deferred_wakes
    R.with_spawns R.with_readers R.with_dormant_bottom R.with_sigma R.with_ranking R.with_last_targets];
  first [reflexivity|
    match goal with E : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- R.side_cells ?next = _ =>
      rewrite (proj1 (@cell_view_get base fr target next next_fr value E)); cell_field_reduction end|
    match goal with E : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- R.contributions ?next = _ =>
      rewrite (proj2 (@cell_view_get base fr target next next_fr value E)); cell_field_reduction end|
    match goal with E : R.dirty_complete_get ?tf ?base ?fr ?target = (?next,?next_fr,?value) |- R.side_cells ?next = _ =>
      rewrite (proj1 (@cell_view_dirty_get tf base fr target next next_fr value E)); cell_field_reduction end|
    match goal with E : R.dirty_complete_get ?tf ?base ?fr ?target = (?next,?next_fr,?value) |- R.contributions ?next = _ =>
      rewrite (proj2 (@cell_view_dirty_get tf base fr target next next_fr value E)); cell_field_reduction end|
    match goal with E : R.set_value ?base ?fr ?input = (?next,?next_fr) |- R.side_cells ?next = _ =>
      rewrite (proj1 (@cell_view_commit base fr input next next_fr E)); cell_field_reduction end|
    match goal with E : R.set_value ?base ?fr ?input = (?next,?next_fr) |- R.contributions ?next = _ =>
      rewrite (proj2 (@cell_view_commit base fr input next next_fr E)); cell_field_reduction end|
    match goal with |- context [R.observe ?base ?target] => unfold R.observe; destruct (Ranks.observe (R.ranking base) target); cell_field_reduction end|
    match goal with |- context [R.materialize ?base ?target] => unfold R.materialize; destruct (M.lookup (R.sigma base) target); cell_field_reduction end|
    match goal with |- context [R.request_spawn ?base ?target] => unfold R.request_spawn; destruct (S.mem target (R.requested_spawns base)); cell_field_reduction end|
    progress unfold R.enqueue,R.enqueue_all,R.mark_side_dirty,R.clear_side_dirty,R.remember_dormant,R.add_reader,R.publish_targets,R.flush_deferred;
      cell_field_reduction|
    match goal with |- context [if ?test then _ else _] => destruct test eqn:?; cell_field_reduction end].
Ltac prove_cell_view := unfold cell_view; split; cell_field_reduction.
Ltac storage_effect_case E :=
  inspect_machine_step E; try discriminate; inversion E; subst;
  first [solve [left; prove_cell_view]|
    match goal with Ew : R.write_side_contribution ?base ?fr ?target ?input = (?next,?changed) |- _ =>
      right; left; unfold side_storage_effect; exists base,fr,target,input,next,changed;
      split; [prove_cell_view|split; [exact Ew|split; [prove_cell_view|cbn [R.cfg_control active_owners R.with_frame_side R.frame_owner]; now left]]] end|
    right; right; unfold close_storage_effect; eexists; eexists; repeat split; reflexivity].
Lemma step_storage_effects tf before after : Sem.step tf before after ->
  cell_view (R.cfg_state before) (R.cfg_state after) \/ side_storage_effect before after \/ close_storage_effect before after.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    unfold Sem.step,R.next_config; cbn [R.cfg_state R.cfg_control]; intro E.
  - storage_effect_case E.
  - destruct seeds; storage_effect_case E.
  - storage_effect_case E.
  - storage_effect_case E.
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      storage_effect_case E.
  - destruct pending; storage_effect_case E.
  - storage_effect_case E.
  - storage_effect_case E.
  - destruct k; storage_effect_case E.
Qed.

(** Dirty reads can write a value without a normal commit. Their pending bit
    is therefore part of the side-update potential, rather than ordinary credit. *)
Lemma get_dirty_map st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  R.dirty_side_targets next = R.dirty_side_targets st.
Proof. unfold R.complete_get; intro E; inversion E; subst; unfold R.materialize; destruct (M.lookup _ _); destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity. Qed.
Lemma side_write_dirty_map st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) ->
  R.dirty_side_targets next = R.dirty_side_targets st.
Proof. unfold R.write_side_contribution; intro E; inversion E; subst; unfold R.promote_side_target; destruct (R.rank_lt _ _ _); reflexivity. Qed.
Lemma commit_dirty_map st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  R.dirty_side_targets next = R.dirty_side_targets st.
Proof. intro E; apply set_value_cases in E as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; reflexivity. Qed.
Lemma dirty_read_is_dirty tf st owner target next : R.try_dirty_read tf st owner target = Some next -> R.is_side_dirty st target = true.
Proof. unfold R.try_dirty_read; destruct (V.eq_dec owner target); [discriminate|]; destruct (R.is_side_dirty st target) eqn:E; [reflexivity|discriminate]. Qed.

(** A fresh initial phase originates only at StartEpisode. Self reevaluation
    and resumed callers inherit an existing frame's phase. *)
Definition frame_lineage before fr :=
  (exists owner k, R.cfg_control before = R.StartEpisode owner k /\
    R.frame_owner fr = owner /\ R.frame_phase fr = U.initial_phase false owner) \/
  exists old, In old (live_frames (R.cfg_control before)) /\
    R.frame_owner fr = R.frame_owner old /\ R.frame_phase fr = R.frame_phase old.
Ltac lineage_case E :=
  inspect_machine_step E; try discriminate; inversion E; subst; wave_phase_metadata;
  cbn [R.cfg_control live_frames suspended_frames] in *; try contradiction;
  repeat match goal with H : In _ (_ :: _) |- _ => destruct H as [<-|H] end; try contradiction;
  match goal with |- frame_lineage ?before ?nextfr =>
    unfold frame_lineage; cbn [R.cfg_control live_frames suspended_frames];
    solve [right; exists nextfr; repeat split; cbn; tauto|
      match goal with Ho : R.frame_owner nextfr = R.frame_owner ?old, Hp : R.frame_phase nextfr = R.frame_phase ?old |- _ =>
        right; exists old; repeat split; cbn; tauto end|
      match goal with |- _ \/ exists old, In old (?head :: ?rest) /\ _ =>
        right; exists head; repeat split; cbn; auto end|
      left; eexists; eexists; repeat split; reflexivity]
  end.
Theorem noncommit_frame_lineage tf before after : outside_commit (R.cfg_control before) ->
  Sem.step tf before after -> forall fr, In fr (live_frames (R.cfg_control after)) -> frame_lineage before fr.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Houtside E new Hin; try contradiction;
    unfold Sem.step,R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - lineage_case E.
  - destruct seeds; lineage_case E.
  - lineage_case E.
  - lineage_case E.
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      lineage_case E.
  - destruct pending; lineage_case E.
  - lineage_case E.
  - destruct k; lineage_case E.
Qed.
Lemma frame_owner_injective frames : NoDup (map R.frame_owner frames) ->
  forall first last, In first frames -> In last frames -> R.frame_owner first = R.frame_owner last -> first = last.
Proof.
  induction frames as [|head tail IH]; cbn; intros Hnd first last Hfirst Hlast Heq; [contradiction|].
  inversion Hnd as [|owner owners Hhead Htail]; subst.
  destruct Hfirst as [<-|Hfirst],Hlast as [<-|Hlast]; [reflexivity| | |exact (IH Htail first last Hfirst Hlast Heq)].
  - exfalso; apply Hhead; rewrite Heq; apply in_map; exact Hlast.
  - exfalso; apply Hhead; rewrite <- Heq; apply in_map; exact Hfirst.
Qed.
Lemma live_frame_owners_distinct st ctrl : sorted_queue st (active_owners ctrl) -> NoDup (map R.frame_owner (live_frames ctrl)).
Proof.
  intro Hsorted; rewrite live_frames_owners; apply ordered_distinct in Hsorted.
  destruct ctrl; cbn [active_owners framed_owners] in *; auto; now inversion Hsorted.
Qed.
Lemma live_frame_unique tf c first last : machine_shape tf c ->
  In first (live_frames (R.cfg_control c)) -> In last (live_frames (R.cfg_control c)) ->
  R.frame_owner first = R.frame_owner last -> first = last.
Proof. intros Hshape; apply frame_owner_injective; exact (@live_frame_owners_distinct _ _ (shape_stack_order Hshape)). Qed.
Theorem noncommit_live_phase tf roots before after first last :
  Sem.steps tf (R.initial_config roots) before -> outside_commit (R.cfg_control before) -> Sem.step tf before after ->
  In first (live_frames (R.cfg_control before)) -> In last (live_frames (R.cfg_control after)) ->
  R.frame_owner last = R.frame_owner first -> R.frame_phase last = R.frame_phase first.
Proof.
  intros Hr Houtside E Hfirst Hlast Howner.
  pose proof (inv_shape (proj2 (@reachable_invariants tf roots before Hr))) as Hshape.
  destruct (@noncommit_frame_lineage tf before after Houtside E last Hlast) as [[owner [k [Hstart [Hnew _]]]]|[old [Hold [Ho Hp]]]].
  - exfalso; pose proof (@live_frames_active _ first Hfirst) as Hactive.
    pose proof (shape_stack_order Hshape) as Hsorted; rewrite Hstart in Hsorted,Hactive.
    cbn [active_owners] in Hsorted,Hactive.
    assert (Hold : In (R.frame_owner first) (suspended_owners k)).
    { rewrite Hstart in Hfirst; change (In first (suspended_frames k)) in Hfirst.
      assert (Hmap : map R.frame_owner (suspended_frames k) = suspended_owners k).
      { exact (@live_frames_owners (R.Return k)). }
      rewrite <- Hmap; apply in_map; exact Hfirst. }
    apply (@stack_owner_not_suspended (R.cfg_state before) owner k Hsorted).
    rewrite <- Hnew,Howner; exact Hold.
  - assert (Hsame : old = first) by (apply (@live_frame_unique tf before old first Hshape Hold Hfirst); congruence).
    now subst old.
Qed.

Module EpisodeCredits (OUL : ORDINARY_UPDATE_TERMINATION_LAWS V D U)
  (SUL : RESTARTING_SIDE_UPDATE_TERMINATION_LAWS V D SU).
Module SC := SideCredits SUL.
Module OC := CommitCredits OUL.
Lemma source_credit_view targets before after source : cell_view before after ->
  SC.source_credit targets after source = SC.source_credit targets before source.
Proof. intros [Hcells Hvalues]; apply sum_nat_ext; intros target _; exact (@SC.credit_layout before after source target Hcells Hvalues). Qed.
Lemma target_credit_view sources before after target : cell_view before after ->
  SC.target_credit sources after target = SC.target_credit sources before target.
Proof. intros [Hcells Hvalues]; apply sum_nat_ext; intros source _; exact (@SC.credit_layout before after source target Hcells Hvalues). Qed.
Lemma closing_above_survivor tf roots before after fr k source :
  Sem.steps tf (R.initial_config roots) before ->
  R.cfg_control before = R.RunDrain fr k -> R.cfg_control after = R.Return k ->
  In source (active_owners (R.cfg_control after)) ->
  R.rank_lt (R.cfg_state before) source (R.frame_owner fr) = true /\ source <> R.frame_owner fr.
Proof.
  intros Hreach Hbefore Hafter Hsource.
  pose proof (inv_shape (proj2 (@reachable_invariants tf roots before Hreach))) as Hshape.
  pose proof (shape_stack_order Hshape) as Hsorted; pose proof (shape_stack_ranks Hshape) as Hranked.
  rewrite Hbefore in Hsorted,Hranked; rewrite Hafter in Hsource;
    cbn [active_owners] in Hsorted,Hranked,Hsource.
  pose proof (@sorted_head_strict (R.cfg_state before) (R.frame_owner fr) (suspended_owners k) source Hsorted Hsource) as Hlt.
  split; [apply (proj2 (@compare_rank _ _ _ (proj1 (Forall_forall _ _) (Forall_inv_tail Hranked) source Hsource) (Forall_inv Hranked))); exact Hlt|intro Heq; subst source; lia].
Qed.
Theorem active_source_credit_step tf roots targets before after source :
  Sem.steps tf (R.initial_config roots) before -> Sem.step tf before after ->
  In source (active_owners (R.cfg_control after)) ->
  SC.source_credit targets (R.cfg_state after) source <= SC.source_credit targets (R.cfg_state before) source.
Proof.
  intros Hreach E Hactive; destruct (@step_storage_effects tf before after E) as [Hview|[Hwrite|Hclose]].
  - rewrite (@source_credit_view targets _ _ source Hview); lia.
  - destruct Hwrite as [base [fr [target [input [next [changed [Hbase [Ewrite [Hnext _]]]]]]]]].
    rewrite (@source_credit_view targets _ _ source Hnext),<- (@source_credit_view targets _ _ source Hbase).
    exact (@SC.source_credit_write targets base fr target input next changed source Ewrite).
  - destruct Hclose as [fr [k [Hbefore [Hafter Hstate]]]].
    destruct (@closing_above_survivor tf roots before after fr k source Hreach Hbefore Hafter Hactive) as [Hlt Hneq].
    rewrite Hstate,(@SC.source_credit_higher_close targets (R.cfg_state before) (R.frame_owner fr) source
      (proj1 (@reachable_scopes tf roots before Hreach)) (or_intror Hlt) Hneq); lia.
Qed.
Definition dirty_credit_relation sources before after := forall target,
  SC.dirty_potential sources after target <= SC.dirty_potential sources before target.
Lemma dirty_credit_layout sources before after target : cell_view before after ->
  R.dirty_side_targets after = R.dirty_side_targets before ->
  SC.dirty_potential sources after target = SC.dirty_potential sources before target.
Proof. intros Hv Hd; unfold SC.dirty_potential,R.is_side_dirty; rewrite (@target_credit_view sources before after target Hv),Hd; reflexivity. Qed.
Lemma dirty_credit_fields sources before after : cell_view before after ->
  R.dirty_side_targets after = R.dirty_side_targets before -> dirty_credit_relation sources before after.
Proof. intros Hv Hd target; rewrite (@dirty_credit_layout sources before after target Hv Hd); lia. Qed.
Lemma dirty_credit_refl sources st : dirty_credit_relation sources st st.
Proof. intro target; lia. Qed.
Lemma dirty_credit_trans sources first middle last : dirty_credit_relation sources first middle ->
  dirty_credit_relation sources middle last -> dirty_credit_relation sources first last.
Proof. intros H H' target; specialize (H target); specialize (H' target); lia. Qed.
Lemma dirty_credit_observe sources st target : dirty_credit_relation sources st (R.observe st target).
Proof. apply dirty_credit_fields; [apply cell_view_observe|unfold R.observe; destruct (Ranks.observe _ _); reflexivity]. Qed.
Lemma dirty_credit_materialize sources st target : dirty_credit_relation sources st (R.materialize st target).
Proof. apply dirty_credit_fields; [apply cell_view_materialize|unfold R.materialize; destruct (M.lookup _ _); reflexivity]. Qed.
Lemma dirty_credit_enqueue sources st target : dirty_credit_relation sources st (R.enqueue st target).
Proof. apply dirty_credit_fields; [split|]; reflexivity. Qed.
Lemma dirty_credit_clear sources st written : dirty_credit_relation sources st (R.clear_side_dirty st written).
Proof. intro target; exact (proj1 (@SC.clear_dirty_potential sources st target written)). Qed.
Lemma dirty_credit_get sources st fr target next next_fr value : R.complete_get st fr target = (next,next_fr,value) ->
  dirty_credit_relation sources st next.
Proof. intro E; apply dirty_credit_fields; [exact (@cell_view_get _ _ _ _ _ _ E)|exact (@get_dirty_map _ _ _ _ _ _ E)]. Qed.
Lemma dirty_credit_finish sources st target value : dirty_credit_relation sources st (dirty_finish st target value).
Proof.
  intro observed; rewrite (@dirty_credit_layout sources
    (R.clear_side_dirty st target) (dirty_finish st target value) observed ltac:(destruct value; split; reflexivity) ltac:(destruct value; reflexivity)).
  exact (proj1 (@SC.clear_dirty_potential sources st observed target)).
Qed.
Lemma dirty_credit_dirty_get sources tf st fr target next next_fr value :
  R.dirty_complete_get tf st fr target = (next,next_fr,value) -> dirty_credit_relation sources st next.
Proof.
  unfold R.dirty_complete_get; set (prepared := R.materialize (if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) target).
  assert (Hp : dirty_credit_relation sources st prepared).
  { apply dirty_credit_fields; unfold prepared,R.materialize; destruct (M.lookup _ _); destruct (R.rank_lt st (R.frame_owner fr) target); try split; reflexivity. }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:Er; intro E; inversion E; subst.
  - destruct (@dirty_read_result tf prepared (R.frame_owner fr) target s Er) as [direct [result [_ [_ [-> _]]]]].
    eapply dirty_credit_trans; [exact Hp|eapply dirty_credit_trans; [apply dirty_credit_finish|apply dirty_credit_fields; [split|]; reflexivity]].
  - eapply dirty_credit_trans; [exact Hp|apply dirty_credit_fields; [split|]; reflexivity].
Qed.
Lemma dirty_credit_write sources st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) -> dirty_credit_relation sources st next.
Proof.
  intros E observed; unfold SC.dirty_potential,R.is_side_dirty; rewrite (@side_write_dirty_map _ _ _ _ _ _ E).
  pose proof (@SC.target_credit_write sources st fr target input next changed observed E); lia.
Qed.
Lemma dirty_credit_write_mark sources st fr target input next :
  R.write_side_contribution st fr target input = (next,true) -> In (R.frame_owner fr) sources ->
  dirty_credit_relation sources st (R.mark_side_dirty next target).
Proof.
  intros E Hsource observed; destruct (V.eq_dec observed target) as [->|Hneq].
  - pose proof (@SC.changed_side_spends_dirty_potential sources st fr target input next E Hsource); lia.
  - unfold SC.dirty_potential; rewrite SC.target_credit_mark,SC.dirty_flag_mark_other by exact Hneq.
    unfold R.is_side_dirty; rewrite (@side_write_dirty_map _ _ _ _ _ _ E).
    pose proof (@SC.target_credit_write sources st fr target input next true observed E); lia.
Qed.
Lemma dirty_credit_commit sources st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  dirty_credit_relation sources st next.
Proof. intro E; apply dirty_credit_fields; [exact (@cell_view_commit _ _ _ _ _ E)|exact (@commit_dirty_map _ _ _ _ _ E)]. Qed.
Ltac dirty_map_fields :=
  cbn [R.cfg_state R.dirty_side_targets R.with_queue R.with_dirty_side_targets R.with_deferred_wakes R.with_spawns
    R.with_readers R.with_dormant_bottom R.with_sigma R.with_ranking R.with_last_targets];
  first [reflexivity|
    match goal with |- context [R.observe ?base ?target] => unfold R.observe; destruct (Ranks.observe (R.ranking base) target); dirty_map_fields end|
    match goal with |- context [R.materialize ?base ?target] => unfold R.materialize; destruct (M.lookup (R.sigma base) target); dirty_map_fields end|
    match goal with |- context [R.request_spawn ?base ?target] => unfold R.request_spawn; destruct (S.mem target (R.requested_spawns base)); dirty_map_fields end|
    progress unfold R.enqueue,R.enqueue_all,R.remember_dormant,R.add_reader,R.publish_targets,R.flush_deferred; dirty_map_fields|
    match goal with |- context [if ?test then _ else _] => destruct test eqn:?; dirty_map_fields end].
Ltac dirty_credit_administration Hsources :=
  cbn [R.cfg_state]; first
    [solve [apply dirty_credit_fields; [prove_cell_view|dirty_map_fields]]|
     match goal with |- dirty_credit_relation ?sources ?before (R.clear_side_dirty ?base ?target) =>
       eapply (@dirty_credit_trans sources before base (R.clear_side_dirty base target)); [dirty_credit_administration Hsources|apply dirty_credit_clear] end|
     match goal with |- dirty_credit_relation ?sources ?before (R.materialize ?base ?target) =>
       eapply (@dirty_credit_trans sources before base (R.materialize base target)); [dirty_credit_administration Hsources|apply dirty_credit_materialize] end|
     match goal with |- dirty_credit_relation ?sources ?before (R.observe ?base ?target) =>
       eapply (@dirty_credit_trans sources before base (R.observe base target)); [dirty_credit_administration Hsources|apply dirty_credit_observe] end|
     match goal with |- dirty_credit_relation ?sources ?before (R.enqueue ?base ?target) =>
       eapply (@dirty_credit_trans sources before base (R.enqueue base target)); [dirty_credit_administration Hsources|apply dirty_credit_enqueue] end|
     match goal with Ew : R.write_side_contribution ?base ?fr ?target ?input = (?next,true) |- dirty_credit_relation ?sources ?before (R.mark_side_dirty ?next ?target) =>
       eapply (@dirty_credit_trans sources before base (R.mark_side_dirty next target));
       [dirty_credit_administration Hsources|apply (@dirty_credit_write_mark sources base fr target input next Ew); apply Hsources; cbn [R.frame_owner R.with_frame_side active_owners]; now left] end|
     match goal with Ew : R.write_side_contribution ?base ?fr ?target ?input = (?next,?changed) |- dirty_credit_relation ?sources ?before ?next =>
       eapply (@dirty_credit_trans sources before base next); [dirty_credit_administration Hsources|exact (@dirty_credit_write sources base fr target input next changed Ew)] end|
     match goal with Eg : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- dirty_credit_relation ?sources ?before ?next =>
       eapply (@dirty_credit_trans sources before base next); [dirty_credit_administration Hsources|exact (@dirty_credit_get sources base fr target next next_fr value Eg)] end|
     match goal with Eg : R.dirty_complete_get ?tf ?base ?fr ?target = (?next,?next_fr,?value) |- dirty_credit_relation ?sources ?before ?next =>
       eapply (@dirty_credit_trans sources before base next); [dirty_credit_administration Hsources|exact (@dirty_credit_dirty_get sources tf base fr target next next_fr value Eg)] end|
     match goal with Es : R.set_value ?base ?fr ?input = (?next,?next_fr) |- dirty_credit_relation ?sources ?before ?next =>
       eapply (@dirty_credit_trans sources before base next); [dirty_credit_administration Hsources|exact (@dirty_credit_commit sources base fr input next next_fr Es)] end|
     match goal with |- context [if ?test then _ else _] => destruct test eqn:?; dirty_credit_administration Hsources end].
Lemma active_supported tf roots (finite : Sem.finite_system tf roots) c owner :
  Sem.steps tf (R.initial_config roots) c -> In owner (active_owners (R.cfg_control c)) -> In owner (Sem.support finite).
Proof.
  intros Hreach Howner; apply (proj1 (@reachable_support tf roots finite c Hreach)).
  exact (proj1 (Forall_forall _ _) (shape_stack_ranks (inv_shape (proj2 (@reachable_invariants tf roots c Hreach)))) owner Howner).
Qed.
Lemma nonclosing_dirty_credit_step sources tf before after :
  (forall owner, In owner (active_owners (R.cfg_control before)) -> In owner sources) ->
  Sem.step tf before after ->
  (forall fr k, R.cfg_control before <> R.RunDrain fr k) ->
  dirty_credit_relation sources (R.cfg_state before) (R.cfg_state after).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hsources E Houtside; try (exfalso; apply (Houtside fr k); reflexivity);
    unfold Sem.step,R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  - inspect_machine_step E; try discriminate; inversion E; subst; dirty_credit_administration Hsources.
  - destruct seeds; inspect_machine_step E; try discriminate; inversion E; subst; dirty_credit_administration Hsources.
  - inspect_machine_step E; try discriminate; inversion E; subst; dirty_credit_administration Hsources.
  - inversion E; subst; dirty_credit_administration Hsources.
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] => destruct (Ranks.lookup order target) eqn:? end;
      inspect_machine_step E; try discriminate; inversion E; subst; dirty_credit_administration Hsources.
  - destruct pending; inspect_machine_step E; try discriminate; inversion E; subst; dirty_credit_administration Hsources.
  - inspect_machine_step E; try discriminate; inversion E; subst; dirty_credit_administration Hsources.
  - destruct k; inspect_machine_step E; try discriminate; inversion E; subst; dirty_credit_administration Hsources.
Qed.

Lemma reset_dirty_flag st scope target : R.is_side_dirty (R.reset_registered_cells st scope) target = R.is_side_dirty st target.
Proof. unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity. Qed.
Lemma reset_dirty_potential sources st scope target : resets_scoped st -> scope_le st target scope ->
  SC.dirty_potential sources (R.reset_registered_cells st scope) target = SC.dirty_potential sources st target.
Proof. intros Hreset Hscope; unfold SC.dirty_potential; rewrite (@SC.target_credit_higher_close sources st scope target Hreset Hscope),reset_dirty_flag; reflexivity. Qed.
Lemma drain_dirty_credit_step sources tf st fr k after target : resets_scoped st ->
  Sem.step tf (configuration st (R.RunDrain fr k)) after ->
  (R.cfg_control after = R.Return k -> scope_le st target (R.frame_owner fr)) ->
  SC.dirty_potential sources (R.cfg_state after) target <= SC.dirty_potential sources st target.
Proof.
  intros Hreset E Hclose; unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control] in E.
  destruct (R.queue st) as [|head tail] eqn:Hqueue; try rewrite Hqueue in E; cbn [R.queue_peek R.queue_pop] in E.
  - inversion E; subst; cbn [R.cfg_state]; rewrite (@reset_dirty_potential sources st (R.frame_owner fr) target Hreset (Hclose eq_refl)); lia.
  - destruct (V.eq_dec head (R.frame_owner fr)) as [Hself|Hother].
    + inversion E; subst; change (SC.dirty_potential sources (R.clear_side_dirty st (R.frame_owner fr)) target <= SC.dirty_potential sources st target).
      exact (proj1 (@SC.clear_dirty_potential sources st target (R.frame_owner fr))).
    + destruct (R.rank_lt st (R.frame_owner fr) head); inversion E; subst; cbn [R.cfg_state];
        [apply Nat.le_refl|rewrite (@reset_dirty_potential sources st (R.frame_owner fr) target Hreset (Hclose eq_refl)); lia].
Qed.
Theorem protected_dirty_credit_step tf roots (finite : Sem.finite_system tf roots) before after target :
  Sem.steps tf (R.initial_config roots) before -> Sem.step tf before after ->
  (forall fr k, R.cfg_control before = R.RunDrain fr k -> R.cfg_control after = R.Return k ->
    scope_le (R.cfg_state before) target (R.frame_owner fr)) ->
  SC.dirty_potential (Sem.support finite) (R.cfg_state after) target <=
    SC.dirty_potential (Sem.support finite) (R.cfg_state before) target.
Proof.
  intros Hreach E Hprotected; destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|current k|fr body k|fr direct pending k|fr direct k|fr k|k];
    try solve [apply (@nonclosing_dirty_credit_step (Sem.support finite) tf _ after
      (fun owner Hin => @active_supported tf roots finite _ owner Hreach Hin) E ltac:(intros other_fr other_k Hbad; cbn [R.cfg_control] in Hbad; discriminate Hbad) target)].
  apply (@drain_dirty_credit_step (Sem.support finite) tf st fr k after target
    (proj1 (@reachable_scopes tf roots _ Hreach)) E).
  intro Hafter; exact (Hprotected fr k eq_refl Hafter).
Qed.
Theorem active_lower_dirty_credit_step tf roots (finite : Sem.finite_system tf roots) before after owner target :
  Sem.steps tf (R.initial_config roots) before -> Sem.step tf before after ->
  In owner (active_owners (R.cfg_control after)) -> scope_le (R.cfg_state before) target owner ->
  SC.dirty_potential (Sem.support finite) (R.cfg_state after) target <=
    SC.dirty_potential (Sem.support finite) (R.cfg_state before) target.
Proof.
  intros Hreach E Hactive Htarget; apply (@protected_dirty_credit_step tf roots finite before after target Hreach E).
  intros fr k Hbefore Hafter.
  destruct (@closing_above_survivor tf roots before after fr k owner Hreach Hbefore Hafter Hactive) as [Hlt _].
  exact (@scope_le_trans (R.cfg_state before) target owner (R.frame_owner fr) Htarget (or_intror Hlt)).
Qed.

(** The trace keeps the owner alive at both ends of every step. A separate
    boundary argument truncates paths when that owner's episode closes. *)
Inductive active_trace tf owner : R.config -> R.config -> Prop :=
| ActiveRefl c : active_trace tf owner c c
| ActiveStep first next last : Sem.step tf first next ->
    In owner (active_owners (R.cfg_control next)) -> active_trace tf owner next last -> active_trace tf owner first last.
Lemma active_trace_path tf owner first last : active_trace tf owner first last -> Sem.steps tf first last.
Proof. intro H; induction H; [constructor|eapply Sem.StepsStep; eassumption]. Qed.
Lemma active_trace_join tf owner first middle last : active_trace tf owner first middle ->
  active_trace tf owner middle last -> active_trace tf owner first last.
Proof. intros H; induction H; intro Htail; [exact Htail|eapply ActiveStep; eauto]. Qed.
Theorem active_source_credit_path tf roots targets owner first last :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  SC.source_credit targets (R.cfg_state last) owner <= SC.source_credit targets (R.cfg_state first) owner.
Proof.
  intros Hr H; revert Hr; induction H; intro Hr; [lia|].
  pose proof (@active_source_credit_step tf roots targets first next owner Hr H H0) as Hstep.
  specialize (IHactive_trace (@path_extend tf _ _ _ Hr H)); lia.
Qed.
Theorem active_lower_dirty_credit_path tf roots (finite : Sem.finite_system tf roots) owner target first last :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  scope_le (R.cfg_state first) target owner ->
  SC.dirty_potential (Sem.support finite) (R.cfg_state last) target <= SC.dirty_potential (Sem.support finite) (R.cfg_state first) target.
Proof.
  intros Hr H; revert Hr; induction H; intros Hr Hscope; [lia|].
  pose proof (@active_lower_dirty_credit_step tf roots finite first next owner target Hr H H0 Hscope) as Hstep.
  specialize (IHactive_trace (@path_extend tf _ _ _ Hr H) (@scope_le_extension _ _ target owner (@step_rank_extension tf _ _ H) Hscope)); lia.
Qed.
Definition promotion_credit st owner := if S.mem owner (R.controlled st) then 0 else 1.
Lemma promotion_credit_path tf first last owner : Sem.steps tf first last -> promotion_credit last.(R.cfg_state) owner <= promotion_credit first.(R.cfg_state) owner.
Proof.
  intro H; pose proof (@path_controlled_extension tf first last H owner) as Hcontrolled.
  unfold promotion_credit; destruct (S.mem owner (R.controlled (R.cfg_state first))) eqn:E;
    [rewrite (Hcontrolled eq_refl)|destruct (S.mem owner (R.controlled (R.cfg_state last)))]; lia.
Qed.
Definition evaluation_credit support owner st := activation_credit support st + SC.source_credit support st owner + promotion_credit st owner.
Theorem evaluation_credit_path tf roots support owner first last :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  evaluation_credit support owner (R.cfg_state last) <= evaluation_credit support owner (R.cfg_state first).
Proof.
  intros Hr H; pose proof (@active_trace_path tf owner first last H) as Hp.
  pose proof (@activation_credit_path support tf first last Hp).
  pose proof (@active_source_credit_path tf roots support owner first last Hr H).
  pose proof (@promotion_credit_path tf first last owner Hp); unfold evaluation_credit; lia.
Qed.
Theorem equal_evaluation_credit tf roots support owner first last :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  evaluation_credit support owner (R.cfg_state last) = evaluation_credit support owner (R.cfg_state first) ->
  activation_credit support (R.cfg_state last) = activation_credit support (R.cfg_state first) /\
  SC.source_credit support (R.cfg_state last) owner = SC.source_credit support (R.cfg_state first) owner /\
  S.mem owner (R.controlled (R.cfg_state last)) = S.mem owner (R.controlled (R.cfg_state first)).
Proof.
  intros Hr H E; pose proof (@active_trace_path tf owner first last H) as Hp.
  pose proof (@activation_credit_path support tf first last Hp) as Ha.
  pose proof (@active_source_credit_path tf roots support owner first last Hr H) as Hs.
  pose proof (@promotion_credit_path tf first last owner Hp) as Hc.
  unfold evaluation_credit in E; split; [lia|split; [lia|]].
  assert (Ec : promotion_credit (R.cfg_state last) owner = promotion_credit (R.cfg_state first) owner) by lia.
  unfold promotion_credit in Ec; destruct (S.mem owner (R.controlled (R.cfg_state last))), (S.mem owner (R.controlled (R.cfg_state first))); congruence.
Qed.

Lemma close_returns_below tf roots first next owner boundary :
  Sem.steps tf (R.initial_config roots) first -> Sem.step tf first next ->
  (exists fr, R.cfg_control first = R.RunDrain fr boundary /\ R.frame_owner fr = owner /\ R.cfg_control next = R.Return boundary) ->
  queue_below (R.cfg_state next) owner.
Proof.
  intros Hr E [fr [Hcontrol [Howner Hreturn]]].
  destruct first as [st ctrl]; cbn [R.cfg_control] in Hcontrol; subst ctrl.
  pose proof (proj2 (@reachable_invariants tf roots _ Hr)) as Hinv.
  pose proof (@closing_queue_under tf roots st fr boundary next Hinv E Hreturn) as Hbelow.
  assert (Hrank : ranked st owner) by (rewrite <- Howner; exact (Forall_inv (shape_stack_ranks (inv_shape Hinv)))).
  unfold queue_below; rewrite <- (@priority_extension st (R.cfg_state next) owner (@step_rank_extension tf _ _ E) Hrank),<- Howner; exact Hbelow.
Qed.
Theorem path_before_episode_return tf roots owner boundary first last :
  Sem.steps tf (R.initial_config roots) first -> episode_live owner boundary (R.cfg_control first) ->
  Sem.steps tf first last ->
  episode_completes tf first owner boundary \/
    (active_trace tf owner first last /\ episode_live owner boundary (R.cfg_control last)).
Proof.
  intros Hr Hl Hp; revert Hr Hl; induction Hp; intros Hr Hl.
  - right; split; [constructor|exact Hl].
  - destruct (@episode_boundary_step tf a b owner boundary Hl H) as [Hlive|Hclose].
    + destruct (IHHp (@path_extend tf _ _ _ Hr H) Hlive) as [Hdone|[Htrace Hlast]].
      * left; destruct Hdone as [final [Htail Hbelow]]; exists final; split; [eapply Sem.StepsStep; eassumption|exact Hbelow].
      * right; split; [eapply ActiveStep; [exact H|exact (@episode_owner_active owner boundary _ Hlive)|exact Htrace]|exact Hlast].
    + left; exists (R.cfg_state b); split.
      * destruct Hclose as [fr [_ [_ Hreturn]]]; destruct b as [st ctrl]; cbn [R.cfg_control] in Hreturn; subst ctrl;
          eapply Sem.StepsStep; [exact H|constructor].
      * exact (@close_returns_below tf roots a b owner boundary Hr H Hclose).
Qed.

(** A shortened dirty read pays for its stored-value change by clearing
    the target's dirty bit, even when its ordinary phase is discarded. *)
Lemma dirty_finish_spends sources st target value :
  R.is_side_dirty st target = true ->
  SC.dirty_potential sources (dirty_finish st target value) target <
    SC.dirty_potential sources st target.
Proof.
  intro Hd; unfold SC.dirty_potential.
  rewrite (@target_credit_view sources st (dirty_finish st target value) target
    (@cell_view_dirty_finish st target value)).
  change (2 * SC.target_credit sources st target +
    (if R.is_side_dirty (dirty_finish st target value) target then 1 else 0) <
    2 * SC.target_credit sources st target + (if R.is_side_dirty st target then 1 else 0)).
  assert (Hclear : R.is_side_dirty (dirty_finish st target value) target = false).
  {
  destruct value; change (R.is_side_dirty (R.clear_side_dirty
    (R.with_queue (R.promote_controlled st target) (R.queue_remove target (R.queue st))) target) target = false);
    apply SC.dirty_flag_clear_same.
  }
  rewrite Hclear,Hd; lia.
Qed.
Lemma dirty_get_spends sources tf st fr target next next_fr value :
  R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  (exists flushed,
    R.try_dirty_read tf
      (R.materialize (if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) target)
      (R.frame_owner fr) target = Some flushed) ->
  SC.dirty_potential sources next target < SC.dirty_potential sources st target.
Proof.
  unfold R.dirty_complete_get; intros E [flushed Er].
  rewrite Er in E; inversion E; subst next next_fr value.
  set (prepared := R.materialize
    (if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) target) in *.
  destruct (@dirty_read_result tf prepared (R.frame_owner fr) target flushed Er)
    as [direct [written [_ [_ [Hresult _]]]]].
  rewrite Hresult.
  rewrite (@dirty_credit_layout sources (dirty_finish prepared target written)
    (R.add_reader (dirty_finish prepared target written) target (R.frame_owner fr)) target
    ltac:(split; reflexivity) eq_refl).
  assert (Hprepared : SC.dirty_potential sources prepared target = SC.dirty_potential sources st target).
  {
  apply dirty_credit_layout; unfold prepared,R.materialize;
      destruct (R.rank_lt st (R.frame_owner fr) target); destruct (M.lookup _ _);
      try split; reflexivity.
  }
  rewrite <- Hprepared; apply dirty_finish_spends; eapply dirty_read_is_dirty; exact Er.
Qed.
Lemma sum_nat_equal_pointwise {A} (xs : list A) before after :
  (forall x, In x xs -> after x <= before x) ->
  sum_nat xs after = sum_nat xs before ->
  forall x, In x xs -> after x = before x.
Proof.
  intros H E x Hin; pose proof (H x Hin).
  destruct (Nat.eq_dec (after x) (before x)); [assumption|].
  pose proof (@sum_nat_strict A xs before after x H Hin ltac:(lia)); lia.
Qed.
(** Freeze the protected targets at a round's entry. Equal activation
    credit keeps this set unchanged; higher closes cannot replenish it. *)
Definition dirty_budget sources targets st := sum_nat targets (SC.dirty_potential sources st).
Theorem active_dirty_budget_path tf roots (finite : Sem.finite_system tf roots)
  owner targets first last :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  Forall (fun target => scope_le (R.cfg_state first) target owner) targets ->
  dirty_budget (Sem.support finite) targets (R.cfg_state last) <=
    dirty_budget (Sem.support finite) targets (R.cfg_state first).
Proof.
  intros Hr H Htargets; apply sum_nat_pointwise; intros target Hin.
  exact (@active_lower_dirty_credit_path tf roots finite owner target first last Hr H
    (proj1 (Forall_forall _ _) Htargets target Hin)).
Qed.
Theorem equal_dirty_budget tf roots (finite : Sem.finite_system tf roots)
  owner targets first last :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  Forall (fun target => scope_le (R.cfg_state first) target owner) targets ->
  dirty_budget (Sem.support finite) targets (R.cfg_state last) =
    dirty_budget (Sem.support finite) targets (R.cfg_state first) ->
  forall target, In target targets ->
    SC.dirty_potential (Sem.support finite) (R.cfg_state last) target =
      SC.dirty_potential (Sem.support finite) (R.cfg_state first) target.
Proof.
  intros Hr H Htargets E; apply sum_nat_equal_pointwise; [|exact E].
  intros target Hin; exact (@active_lower_dirty_credit_path tf roots finite owner target
    first last Hr H (proj1 (Forall_forall _ _) Htargets target Hin)).
Qed.
Definition protected_targets support st owner :=
  filter (fun target => if V.eq_dec target owner then true else R.rank_lt st target owner) support.
Lemma protected_targets_spec support st owner target :
  In target (protected_targets support st owner) <-> In target support /\ scope_le st target owner.
Proof.
  unfold protected_targets; rewrite filter_In; unfold scope_le.
  destruct (V.eq_dec target owner); intuition congruence.
Qed.
Lemma protected_targets_scoped support st owner :
  Forall (fun target => scope_le st target owner) (protected_targets support st owner).
Proof.
  apply Forall_forall; intros target Hin; exact (proj2 (proj1
    (@protected_targets_spec support st owner target) Hin)).
Qed.
Lemma protected_owner support st owner : In owner support ->
  In owner (protected_targets support st owner).
Proof.
  intro H; apply protected_targets_spec; split; [exact H|now left].
Qed.
Lemma equal_dirty_get_value sources tf st fr target next next_fr value owner :
  R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  SC.dirty_potential sources next owner = SC.dirty_potential sources st owner ->
  R.sigma_value next owner = R.sigma_value st owner.
Proof.
  intros E Hcredit; destruct (V.eq_dec owner target) as [->|Hneq].
  -   unfold R.dirty_complete_get in E.
  set (prepared := R.materialize (if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) target) in *.
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:Er.
  +   exfalso; pose proof (@dirty_get_spends sources tf st fr target next next_fr value
        ltac:(unfold R.dirty_complete_get; fold prepared; rewrite Er; exact E)
        ltac:(exists s; exact Er)); lia.
  +   inversion E; subst; change (R.sigma_value prepared target = R.sigma_value st target).
  unfold prepared; rewrite materialize_valuation; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
  -   unfold R.dirty_complete_get in E.
  set (prepared := R.materialize (if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) target) in *.
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:Er;
      inversion E; subst; cbn [R.add_reader R.with_readers R.sigma].
  +   destruct (@dirty_read_result tf prepared (R.frame_owner fr) target s Er)
        as [direct [written [_ [_ [-> _]]]]].
  change (R.sigma_value (dirty_finish prepared target written) owner = R.sigma_value st owner).
  rewrite dirty_finish_sigma_other by exact Hneq.
  unfold prepared; rewrite materialize_valuation; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
  +   change (R.sigma_value prepared owner = R.sigma_value st owner).
  unfold prepared; rewrite materialize_valuation; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
Qed.

(** Equal protected potential excludes noncommit changes to a live
    owner's value, including dirty reads performed by a nested child. *)
Lemma materialized_not_dormant st owner : R.is_materialized st owner = true ->
  R.is_dormant st owner = false.
Proof.
  unfold R.is_materialized,R.is_dormant; destruct (M.lookup (R.sigma st) owner); cbn; intros; rewrite ?andb_false_r; congruence.
Qed.
Lemma dormant_publish_other st target changed owner : owner <> target ->
  R.sigma_value (R.publish_dormant_target st target changed) owner = R.sigma_value st owner.
Proof.
  intro Hneq; unfold R.publish_dormant_target; destruct changed.
  - change (R.sigma_value (R.with_sigma (R.materialize st target)
      (M.update (R.sigma (R.materialize st target)) target (R.aggregate st target))) owner =
      R.sigma_value st owner).
    rewrite sigma_write_other by congruence; apply materialize_valuation.
  - apply materialize_valuation.
Qed.
Lemma equal_dirty_get_observe sources tf st fr target next next_fr value owner :
  R.dirty_complete_get tf (R.observe st target) fr target = (next,next_fr,value) ->
  SC.dirty_potential sources next owner = SC.dirty_potential sources st owner ->
  R.sigma_value next owner = R.sigma_value st owner.
Proof.
  intros E Hcredit.
  rewrite <- (@precision_values st (R.observe st target) (precision_data_observe st target) owner).
  apply (@equal_dirty_get_value sources tf (R.observe st target) fr target next next_fr value owner E).
  rewrite (@dirty_credit_layout sources st (R.observe st target) owner
    (cell_view_observe st target) ltac:(unfold R.observe; destruct (Ranks.observe _ _); reflexivity)).
  exact Hcredit.
Qed.
Lemma side_write_valuation st fr target input next changed owner :
  R.write_side_contribution st fr target input = (next,changed) ->
  R.sigma_value next owner = R.sigma_value st owner.
Proof. intro E; unfold R.sigma_value; now rewrite (@side_write_sigma st fr target input next changed E). Qed.
Ltac stable_value_administration :=
  first [reflexivity|
    match goal with Eg : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- R.sigma_value ?next ?owner = _ =>
      rewrite (@precision_values base next (precision_data_get Eg) owner); stable_value_administration end|
    match goal with Eg : R.dirty_complete_get ?tf (R.observe ?base ?target) ?fr ?target = (?next,?next_fr,?value),
      Ec : SC.dirty_potential ?sources ?next ?owner = SC.dirty_potential ?sources ?base ?owner |- R.sigma_value ?next ?owner = _ =>
      exact (@equal_dirty_get_observe sources tf base fr target next next_fr value owner Eg Ec) end|
    match goal with Ew : R.write_side_contribution ?base ?fr ?target ?input = (?next,?changed) |- R.sigma_value ?next ?owner = _ =>
      rewrite (@side_write_valuation base fr target input next changed owner Ew); stable_value_administration end|
    progress rewrite materialize_valuation; stable_value_administration|
    match goal with |- context [R.observe ?base ?target] => rewrite (@precision_values base (R.observe base target) (precision_data_observe base target)); stable_value_administration end|
    match goal with |- context [R.request_spawn ?base ?target] => rewrite (@precision_values base (R.request_spawn base target) (precision_data_request base target)); stable_value_administration end|
    match goal with |- context [R.reset_registered_cells ?base ?target] => rewrite (@precision_values base (R.reset_registered_cells base target) (precision_data_reset base target)); stable_value_administration end|
    match goal with |- R.sigma_value ?next ?owner = R.sigma_value ?old ?owner =>
      first [
        match next with R.clear_side_dirty ?base ?target =>
          change (R.sigma_value base owner = R.sigma_value old owner) end |
        match next with R.mark_side_dirty ?base ?target =>
          change (R.sigma_value base owner = R.sigma_value old owner) end |
        match next with R.with_queue ?base ?queue =>
          change (R.sigma_value base owner = R.sigma_value old owner) end |
        match next with R.add_reader ?base ?target ?reader =>
          change (R.sigma_value base owner = R.sigma_value old owner) end |
        match next with R.publish_targets ?base ?fr =>
          change (R.sigma_value base owner = R.sigma_value old owner) end |
        match next with R.remember_dormant ?base ?target =>
          change (R.sigma_value base owner = R.sigma_value old owner) end |
        match next with R.enqueue ?base ?target =>
          change (R.sigma_value base owner = R.sigma_value old owner) end |
        match next with R.flush_deferred ?base =>
          change (R.sigma_value base owner = R.sigma_value old owner) end ];
      stable_value_administration end|
    match goal with |- context [R.publish_dormant_target ?base ?target ?changed] =>
      rewrite (@dormant_publish_other base target changed _ ltac:(intro Heq; subst;
        match goal with Hd : R.is_dormant ?old ?x = true, Hm : R.is_materialized ?old ?x = true |- _ =>
          rewrite (materialized_not_dormant Hm) in Hd; discriminate end)); stable_value_administration end|
    match goal with |- context [if ?test then _ else _] => destruct test eqn:?; stable_value_administration end].
Ltac stable_value_case E :=
  inspect_machine_step E; try discriminate; inversion E; subst;
  cbn [R.cfg_state] in *; stable_value_administration.
Lemma equal_dirty_noncommit_value sources tf before after owner :
  R.is_materialized (R.cfg_state before) owner = true ->
  outside_commit (R.cfg_control before) -> Sem.step tf before after ->
  SC.dirty_potential sources (R.cfg_state after) owner =
    SC.dirty_potential sources (R.cfg_state before) owner ->
  R.sigma_value (R.cfg_state after) owner = R.sigma_value (R.cfg_state before) owner.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|current k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hmat Houtside E Hcredit; try contradiction;
    unfold Sem.step,R.next_config in E; cbn [R.cfg_state R.cfg_control] in E,Hmat,Hcredit |- *.
  - stable_value_case E.
  - destruct seeds; stable_value_case E.
  - stable_value_case E.
  - stable_value_case E.
  - destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] =>
      destruct (Ranks.lookup order target) eqn:? end; stable_value_case E.
  - destruct pending; stable_value_case E.
  - stable_value_case E.
  - destruct k; stable_value_case E.
Qed.
Definition live_materialized c := forall fr, In fr (live_frames (R.cfg_control c)) ->
  R.is_materialized (R.cfg_state c) (R.frame_owner fr) = true.
Lemma live_materialized_step tf before after :
  live_materialized before -> Sem.step tf before after -> live_materialized after.
Proof.
  intros Hlive E next_fr Hnext.
  pose proof (@next_materialized_extension tf before after E) as Hgrowth.
  destruct (R.cfg_control before) eqn:Hcontrol;
    try assert (Houtside : outside_commit (R.cfg_control before)) by (rewrite Hcontrol; exact I).
  all: try solve [
    destruct (@noncommit_frame_lineage tf before after Houtside E next_fr Hnext)
      as [[owner [k [Hstart [Howner Hphase]]]]|[old [Hold [Howner Hphase]]]];
    [unfold Sem.step,R.next_config in E; rewrite Hstart in E; inversion E;
      subst after; cbn [R.cfg_state]; rewrite Howner;
      change (R.is_materialized (R.materialize (R.cfg_state before) owner) owner = true);
      apply materialize_live|
     rewrite Howner; apply Hgrowth; exact (Hlive old Hold)]].
  unfold Sem.step,R.next_config in E; rewrite Hcontrol in E.
  destruct (R.set_value (R.flush_deferred (R.cfg_state before)) f t) as [next committed_fr] eqn:Eset.
  inversion E; subst after; cbn [R.cfg_control live_frames] in Hnext.
  destruct Hnext as [<-|Hin].
  - cbn [R.cfg_state]; rewrite (@set_value_owner _ _ _ _ _ Eset).
    apply Hgrowth; apply Hlive; rewrite Hcontrol; cbn; now left.
  - cbn [R.cfg_state]; apply Hgrowth; apply Hlive; rewrite Hcontrol; cbn; now right.
Qed.
Theorem reachable_live_materialized tf roots c :
  Sem.steps tf (R.initial_config roots) c -> live_materialized c.
Proof.
  assert (Hwalk : forall first last, Sem.steps tf first last ->
    live_materialized first -> live_materialized last).
  { intros first last H; induction H; intro Hl; [exact Hl|apply IHsteps; eapply live_materialized_step; eassumption]. }
  intro Hr; apply (Hwalk _ _ Hr); intros fr Hin; contradiction.
Qed.
(** Ordinary update credit is the last component: promotion, activation,
    side changes, and dirty reads are paid by the earlier components. *)
Definition ordinary_credit st fr := if S.mem (R.frame_owner fr) (R.controlled st)
  then OUL.remaining_changes (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr)) else 0.
Lemma equal_noncommit_ordinary_credit sources tf roots before after first last :
  Sem.steps tf (R.initial_config roots) before -> outside_commit (R.cfg_control before) ->
  Sem.step tf before after ->
  In first (live_frames (R.cfg_control before)) -> In last (live_frames (R.cfg_control after)) ->
  R.frame_owner last = R.frame_owner first ->
  S.mem (R.frame_owner first) (R.controlled (R.cfg_state after)) =
    S.mem (R.frame_owner first) (R.controlled (R.cfg_state before)) ->
  SC.dirty_potential sources (R.cfg_state after) (R.frame_owner first) =
    SC.dirty_potential sources (R.cfg_state before) (R.frame_owner first) ->
  ordinary_credit (R.cfg_state after) last = ordinary_credit (R.cfg_state before) first.
Proof.
  intros Hr Ho E Hfirst Hlast Howner Hcontrolled Hdirty.
  unfold ordinary_credit; rewrite Howner,Hcontrolled.
  rewrite (@noncommit_live_phase tf roots before after first last Hr Ho E Hfirst Hlast Howner).
  rewrite (@equal_dirty_noncommit_value sources tf before after (R.frame_owner first)
    (@reachable_live_materialized tf roots before Hr first Hfirst) Ho E Hdirty); reflexivity.
Qed.

Lemma commit_ordinary_credit tf roots st fr direct k after first last :
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) ->
  Sem.step tf (configuration st (R.RunCommit fr direct k)) after ->
  In first (live_frames (R.RunCommit fr direct k)) ->
  In last (live_frames (R.cfg_control after)) ->
  R.frame_owner last = R.frame_owner first ->
  S.mem (R.frame_owner first) (R.controlled (R.cfg_state after)) =
    S.mem (R.frame_owner first) (R.controlled st) ->
  ordinary_credit (R.cfg_state after) last <= ordinary_credit st first.
Proof.
  intros Hr E Hfirst Hlast Howner Hcontrolled.
  unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control] in E.
  destruct (R.set_value (R.flush_deferred st) fr direct) as [next next_fr] eqn:Eset.
  inversion E; subst after; cbn [R.cfg_control live_frames] in Hlast.
  pose proof (inv_shape (proj2 (@reachable_invariants tf roots _ Hr))) as Hshape.
  destruct Hlast as [<-|Hlast].
  - assert (Hsame : first = fr).
    { apply (@live_frame_unique tf _ first fr Hshape Hfirst ltac:(cbn; now left)).
      rewrite <- Howner; exact (@set_value_owner _ _ _ _ _ Eset). }
    subst first; unfold ordinary_credit; rewrite (@set_value_owner _ _ _ _ _ Eset).
    cbn [R.cfg_state] in Hcontrolled; rewrite (@set_value_owner _ _ _ _ _ Eset) in Howner.
    cbn [R.cfg_state]; rewrite Hcontrolled.
    destruct (S.mem (R.frame_owner fr) (R.controlled st)) eqn:Hc; [|lia].
    exact (@OC.controlled_commit_credit (R.flush_deferred st) fr direct next next_fr Eset Hc).
  - assert (Hsame : first = last).
    { apply (@live_frame_unique tf _ first last Hshape Hfirst ltac:(cbn; now right)); symmetry; exact Howner. }
    subst first; unfold ordinary_credit; cbn [R.cfg_state] in Hcontrolled |- *; rewrite Hcontrolled.
    destruct (S.mem (R.frame_owner last) (R.controlled st)); [|lia].
    assert (Hneq : R.frame_owner last <> R.frame_owner fr).
    { intro Heq; assert (Hsame : last = fr).
      { apply (@live_frame_unique tf _ last fr Hshape ltac:(cbn; now right) ltac:(cbn; now left) Heq). }
      subst last; pose proof (shape_stack_order Hshape) as Hsorted.
      apply (@stack_owner_not_suspended st (R.frame_owner fr) k Hsorted).
      change (In (R.frame_owner fr) (framed_owners (R.Return k))).
      rewrite <- (@live_frames_owners (R.Return k)); apply in_map; exact Hlast. }
    rewrite (@set_value_valuation_other _ _ _ _ _ Eset _ Hneq).
    change (OUL.remaining_changes (R.frame_phase last) (R.sigma_value st (R.frame_owner last)) <=
      OUL.remaining_changes (R.frame_phase last) (R.sigma_value st (R.frame_owner last))); lia.
Qed.
Theorem ordinary_credit_step sources tf roots before after first last :
  Sem.steps tf (R.initial_config roots) before -> Sem.step tf before after ->
  In first (live_frames (R.cfg_control before)) -> In last (live_frames (R.cfg_control after)) ->
  R.frame_owner last = R.frame_owner first ->
  S.mem (R.frame_owner first) (R.controlled (R.cfg_state after)) =
    S.mem (R.frame_owner first) (R.controlled (R.cfg_state before)) ->
  SC.dirty_potential sources (R.cfg_state after) (R.frame_owner first) =
    SC.dirty_potential sources (R.cfg_state before) (R.frame_owner first) ->
  ordinary_credit (R.cfg_state after) last <= ordinary_credit (R.cfg_state before) first.
Proof.
  intros Hr E Hfirst Hlast Howner Hcontrolled Hdirty.
  destruct before as [st ctrl]; destruct ctrl;
    try solve [rewrite (@equal_noncommit_ordinary_credit sources tf roots _ after first last
      Hr I E Hfirst Hlast Howner Hcontrolled Hdirty); lia].
  exact (@commit_ordinary_credit tf roots st f t c after first last Hr E Hfirst Hlast Howner Hcontrolled).
Qed.

Lemma step_framed_owner tf before after owner :
  Sem.step tf before after -> In owner (framed_owners (R.cfg_control before)) ->
  In owner (active_owners (R.cfg_control after)) ->
  In owner (framed_owners (R.cfg_control after)).
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|current k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros E Hin Hactive; cbn [R.cfg_control framed_owners] in Hin; try contradiction;
    unfold Sem.step,R.next_config in E; cbn [R.cfg_state R.cfg_control] in E.
  all: try destruct body; try destruct pending; try destruct k.
  all: repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] =>
    destruct (Ranks.lookup order target) eqn:? end.
  all: inspect_machine_step E; try discriminate; inversion E; subst; wave_phase_metadata.
  all: cbn [R.cfg_control active_owners framed_owners R.fresh_frame R.frame_owner
    R.with_frame_side R.with_frame_read R.with_frame_phase] in *; intuition congruence.
Qed.
Lemma active_frame_survives tf before after fr :
  Sem.step tf before after -> In fr (live_frames (R.cfg_control before)) ->
  In (R.frame_owner fr) (active_owners (R.cfg_control after)) ->
  exists next_fr, In next_fr (live_frames (R.cfg_control after)) /\
    R.frame_owner next_fr = R.frame_owner fr.
Proof.
  intros E Hfirst Hactive.
  assert (Hin : In (R.frame_owner fr) (framed_owners (R.cfg_control after))).
  { eapply step_framed_owner; [exact E| |exact Hactive].
    rewrite <- live_frames_owners; apply in_map; exact Hfirst. }
  rewrite <- live_frames_owners in Hin; apply in_map_iff in Hin as [next_fr [Howner Hnext]].
  exists next_fr; auto.
Qed.

Theorem ordinary_credit_path tf roots (finite : Sem.finite_system tf roots)
  owner first last first_fr last_fr :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  In first_fr (live_frames (R.cfg_control first)) -> R.frame_owner first_fr = owner ->
  In last_fr (live_frames (R.cfg_control last)) -> R.frame_owner last_fr = owner ->
  evaluation_credit (Sem.support finite) owner (R.cfg_state last) =
    evaluation_credit (Sem.support finite) owner (R.cfg_state first) ->
  SC.dirty_potential (Sem.support finite) (R.cfg_state last) owner =
    SC.dirty_potential (Sem.support finite) (R.cfg_state first) owner ->
  ordinary_credit (R.cfg_state last) last_fr <= ordinary_credit (R.cfg_state first) first_fr.
Proof.
  intros Hr H; revert first_fr last_fr Hr; induction H;
    intros first_fr last_fr Hr Hfirst Hfirst_owner Hlast Hlast_owner Heval Hdirty.
  - assert (Hsame : first_fr = last_fr).
    { apply (@live_frame_unique tf c first_fr last_fr
        (inv_shape (proj2 (@reachable_invariants tf roots c Hr))) Hfirst Hlast); congruence. }
    subst; lia.
  - assert (Hnext : Sem.steps tf (R.initial_config roots) next) by (eapply path_extend; eassumption).
    assert (Hprefix : active_trace tf owner first next) by (eapply ActiveStep; [exact H|exact H0|constructor]).
    pose proof (@evaluation_credit_path tf roots (Sem.support finite) owner first next Hr Hprefix) as Heval_step.
    pose proof (@evaluation_credit_path tf roots (Sem.support finite) owner next last Hnext H1) as Heval_tail.
    pose proof (@active_lower_dirty_credit_step tf roots finite first next owner owner Hr H H0 (or_introl eq_refl)) as Hdirty_step.
    pose proof (@active_lower_dirty_credit_path tf roots finite owner owner next last Hnext H1 (or_introl eq_refl)) as Hdirty_tail.
    assert (Eeval : evaluation_credit (Sem.support finite) owner (R.cfg_state next) =
      evaluation_credit (Sem.support finite) owner (R.cfg_state first)) by lia.
    assert (Edirty : SC.dirty_potential (Sem.support finite) (R.cfg_state next) owner =
      SC.dirty_potential (Sem.support finite) (R.cfg_state first) owner) by lia.
    destruct (@active_frame_survives tf first next first_fr H Hfirst ltac:(now rewrite Hfirst_owner))
      as [next_fr [Hframe Hframe_owner]].
    pose proof (proj2 (proj2 (@equal_evaluation_credit tf roots (Sem.support finite) owner
      first next Hr Hprefix Eeval))) as Hcontrolled.
    assert (Hcredit_step : ordinary_credit (R.cfg_state next) next_fr <= ordinary_credit (R.cfg_state first) first_fr).
    { apply (@ordinary_credit_step (Sem.support finite) tf roots first next first_fr next_fr
        Hr H Hfirst Hframe Hframe_owner); now rewrite Hfirst_owner. }
    specialize (IHactive_trace next_fr last_fr Hnext Hframe ltac:(congruence)
      Hlast Hlast_owner ltac:(lia) ltac:(lia)); lia.
Qed.
Corollary equal_dirty_noncommit_path tf roots (finite : Sem.finite_system tf roots)
  owner first last fr :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  In fr (live_frames (R.cfg_control first)) -> R.frame_owner fr = owner ->
  (forall before after, Sem.steps tf first before -> Sem.step tf before after ->
    Sem.steps tf after last -> outside_commit (R.cfg_control before)) ->
  SC.dirty_potential (Sem.support finite) (R.cfg_state last) owner =
    SC.dirty_potential (Sem.support finite) (R.cfg_state first) owner ->
  R.sigma_value (R.cfg_state last) owner = R.sigma_value (R.cfg_state first) owner.
Proof.
  intros Hr H Hframe Howner Houtside Hdirty.
  pose proof (@reachable_live_materialized tf roots first Hr fr Hframe) as Hmat.
  rewrite Howner in Hmat; clear fr Hframe Howner.
  revert Hr Hmat Houtside Hdirty; induction H; intros Hr Hmat Houtside Hdirty; [reflexivity|].
  assert (Hnext : Sem.steps tf (R.initial_config roots) next) by (eapply path_extend; eassumption).
  pose proof (@active_lower_dirty_credit_step tf roots finite first next owner owner Hr H H0 (or_introl eq_refl)) as Hstep.
  pose proof (@active_lower_dirty_credit_path tf roots finite owner owner next last Hnext H1 (or_introl eq_refl)) as Htail.
  rewrite (IHactive_trace Hnext (@next_materialized_extension tf first next H owner Hmat)
    ltac:(intros before after Hb E Ha; apply (Houtside before after); [eapply Sem.StepsStep; eassumption|exact E|exact Ha])
    ltac:(lia)).
  apply (@equal_dirty_noncommit_value (Sem.support finite) tf first next owner Hmat
    (Houtside first next (@Sem.StepsRefl tf first) H (@active_trace_path tf owner next last H1)) H); lia.
Qed.

(** The ordering allows a later component to increase only when an
    earlier one strictly decreases. No uniform bound on phase credit is
    needed. *)
Definition credit_vector := (nat * (nat * nat))%type.
Definition credit_lt (small large : credit_vector) :=
  fst small < fst large \/
  (fst small = fst large /\
    (fst (snd small) < fst (snd large) \/
      (fst (snd small) = fst (snd large) /\ snd (snd small) < snd (snd large)))).
Lemma credit_lt_well_founded : well_founded credit_lt.
Proof.
  intros [evaluation [dirty ordinary]]; revert dirty ordinary.
  induction evaluation using lt_wf_ind; intro dirty.
  induction dirty using lt_wf_ind; intro ordinary.
  induction ordinary using lt_wf_ind; constructor; intros [next_evaluation [next_dirty next_ordinary]] Hlt.
  unfold credit_lt in Hlt; cbn in Hlt.
  destruct Hlt as [Hevaluation|[-> [Hdirty|[-> Hordinary]]]].
  - exact (H next_evaluation Hevaluation next_dirty next_ordinary).
  - exact (H0 next_dirty Hdirty next_ordinary).
  - exact (H1 next_ordinary Hordinary).
Qed.
Lemma credit_lt_trans first middle last :
  credit_lt first middle -> credit_lt middle last -> credit_lt first last.
Proof.
  destruct first as [a [b c]],middle as [d [e f]],last as [g [h i]];
    unfold credit_lt; cbn; intros; intuition lia.
Qed.
Definition round_budget support targets st fr : credit_vector :=
  (evaluation_credit support (R.frame_owner fr) st,
    (dirty_budget support targets st, ordinary_credit st fr)).
Theorem round_budget_path tf roots (finite : Sem.finite_system tf roots)
  owner targets first last first_fr last_fr :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  In first_fr (live_frames (R.cfg_control first)) -> R.frame_owner first_fr = owner ->
  In last_fr (live_frames (R.cfg_control last)) -> R.frame_owner last_fr = owner ->
  Forall (fun target => scope_le (R.cfg_state first) target owner) targets ->
  In owner targets ->
  round_budget (Sem.support finite) targets (R.cfg_state last) last_fr =
    round_budget (Sem.support finite) targets (R.cfg_state first) first_fr \/
  credit_lt (round_budget (Sem.support finite) targets (R.cfg_state last) last_fr)
    (round_budget (Sem.support finite) targets (R.cfg_state first) first_fr).
Proof.
  intros Hr H Hfirst Hfirst_owner Hlast Hlast_owner Htargets Howner.
  pose proof (@evaluation_credit_path tf roots (Sem.support finite) owner first last Hr H) as Hevaluation.
  pose proof (@active_dirty_budget_path tf roots finite owner targets first last Hr H Htargets) as Hdirty.
  destruct (Nat.eq_dec
    (evaluation_credit (Sem.support finite) owner (R.cfg_state last))
    (evaluation_credit (Sem.support finite) owner (R.cfg_state first))) as [Eevaluation|Estrict].
  - destruct (Nat.eq_dec (dirty_budget (Sem.support finite) targets (R.cfg_state last))
      (dirty_budget (Sem.support finite) targets (R.cfg_state first))) as [Edirty|Estrict_dirty].
    + pose proof (@equal_dirty_budget tf roots finite owner targets first last Hr H Htargets Edirty owner Howner) as Eowner.
      pose proof (@ordinary_credit_path tf roots finite owner first last first_fr last_fr
        Hr H Hfirst Hfirst_owner Hlast Hlast_owner Eevaluation Eowner) as Hordinary.
      destruct (Nat.eq_dec (ordinary_credit (R.cfg_state last) last_fr)
        (ordinary_credit (R.cfg_state first) first_fr)) as [Eordinary|Estrict_ordinary].
      * left; unfold round_budget; rewrite Hfirst_owner,Hlast_owner,Eevaluation,Edirty,Eordinary; reflexivity.
      * right; unfold credit_lt,round_budget; rewrite Hfirst_owner,Hlast_owner; cbn; right; split; [exact Eevaluation|right; split; [exact Edirty|lia]].
    + right; unfold credit_lt,round_budget; rewrite Hfirst_owner,Hlast_owner; cbn; right; split; [exact Eevaluation|left; lia].
  - right; unfold credit_lt,round_budget; rewrite Hfirst_owner,Hlast_owner; cbn; left; lia.
Qed.
Lemma commit_controlled_map st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) -> R.controlled next = R.controlled st.
Proof.
  intro E; apply set_value_cases in E as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; reflexivity.
Qed.

Lemma commit_materialized_exact st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) ->
  R.is_materialized st (R.frame_owner fr) = true ->
  forall target, R.is_materialized next target = R.is_materialized st target.
Proof.
  intros E Hmat target; destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq].
  -   rewrite Hmat; exact (@materialized_commit st fr direct next next_fr E (R.frame_owner fr) Hmat).
  -   unfold R.is_materialized; now rewrite (@set_value_sigma_other _ _ _ _ _ E target Hneq).
Qed.

Lemma commit_activation_exact support st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) ->
  R.is_materialized st (R.frame_owner fr) = true ->
  activation_credit support next = activation_credit support st.
Proof.
  intros E Hmat; unfold activation_credit,discovery_credit,unmaterialized_credit.
  rewrite (proj1 (@set_value_metadata st fr direct next next_fr E)).
  f_equal; apply sum_nat_ext; intros target _;
    now rewrite (@commit_materialized_exact st fr direct next next_fr E Hmat target).
Qed.

Lemma controlled_commit_ordinary_strict st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) ->
  S.mem (R.frame_owner fr) (R.controlled st) = true ->
  ~ eqv (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) ->
  ordinary_credit next next_fr < ordinary_credit st fr.
Proof.
  intros E Hc Hchange; unfold ordinary_credit; rewrite (@set_value_owner _ _ _ _ _ E),
    (@commit_controlled_map _ _ _ _ _ E),Hc.
  exact (@OC.changed_controlled_commit_consumes st fr direct next next_fr E Hc Hchange).
Qed.

Theorem paid_commit_spends support targets st fr direct next next_fr :
  R.is_materialized st (R.frame_owner fr) = true ->
  R.set_value (R.flush_deferred st) fr direct = (next,next_fr) ->
  S.mem (R.frame_owner fr) (R.controlled st) = true ->
  ~ eqv (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) ->
  credit_lt (round_budget support targets next next_fr) (round_budget support targets st fr).
Proof.
  intros Hmat E Hc Hchange.
  assert (Heval : evaluation_credit support (R.frame_owner fr) next =
    evaluation_credit support (R.frame_owner fr) st).
  {
  unfold evaluation_credit; rewrite (@commit_activation_exact support _ _ _ _ _ E Hmat).
  rewrite (@source_credit_view support _ _ (R.frame_owner fr) (@cell_view_commit _ _ _ _ _ E)).
  unfold promotion_credit; rewrite (@commit_controlled_map _ _ _ _ _ E); reflexivity.
  }
  assert (Hdirty : dirty_budget support targets next = dirty_budget support targets st).
  {
  apply sum_nat_ext; intros target _; rewrite (@dirty_credit_layout support _ _ target
      (@cell_view_commit _ _ _ _ _ E) (@commit_dirty_map _ _ _ _ _ E)); reflexivity.
  }
  pose proof (@controlled_commit_ordinary_strict _ _ _ _ _ E Hc Hchange) as Hordinary.
  change (ordinary_credit next next_fr < ordinary_credit st fr) in Hordinary.
  unfold credit_lt,round_budget; rewrite (@set_value_owner _ _ _ _ _ E); cbn.
  right; split; [exact Heval|right; split; assumption].
Qed.

Lemma credit_lt_absorb first middle last :
  (first = middle \/ credit_lt first middle) ->
  (middle = last \/ credit_lt middle last) ->
  (first = last \/ credit_lt first last).
Proof.
  intros [->|Hfirst] [->|Hlast]; auto; right; eapply credit_lt_trans; eassumption.
Qed.

(** Dirty work remains queued until its episode starts. StartEpisode
    clears that one pending bit before evaluating any transfer body. *)
Definition dirty_queued st := forall target, R.is_side_dirty st target = true -> In target (R.queue st).
Definition dirty_scheduled c := forall target, R.is_side_dirty (R.cfg_state c) target = true ->
  In target (R.queue (R.cfg_state c)) \/ exists k, R.cfg_control c = R.StartEpisode target k.
Lemma dirty_queued_fields before after :
  R.dirty_side_targets after = R.dirty_side_targets before ->
  R.queue after = R.queue before -> dirty_queued before -> dirty_queued after.
Proof.
  unfold dirty_queued,R.is_side_dirty; intros Hd Hq H; now rewrite Hd,Hq.
Qed.

Lemma dirty_queued_grows before after :
  R.dirty_side_targets after = R.dirty_side_targets before ->
  (forall target, In target (R.queue before) -> In target (R.queue after)) ->
  dirty_queued before -> dirty_queued after.
Proof.
  unfold dirty_queued,R.is_side_dirty; intros Hd Hq H target Hdirty; rewrite Hd in Hdirty; now apply Hq,H.
Qed.

Lemma dirty_queued_clear st written : dirty_queued st -> dirty_queued (R.clear_side_dirty st written).
Proof.
  intros H target Hd; destruct (V.eq_dec target written) as [->|Hneq].
  -   rewrite SC.dirty_flag_clear_same in Hd; discriminate.
  -   rewrite SC.dirty_flag_clear_other in Hd by exact Hneq; exact (H target Hd).
Qed.

Lemma dirty_queued_finish st target value : dirty_queued st -> dirty_queued (dirty_finish st target value).
Proof.
  intros H observed Hd; destruct (V.eq_dec observed target) as [->|Hneq].
  -   assert (Hclear : R.is_side_dirty (dirty_finish st target value) target = false).
  {
  destruct value; change (R.is_side_dirty (R.clear_side_dirty
        (R.with_queue (R.promote_controlled st target) (R.queue_remove target (R.queue st))) target) target = false);
        apply SC.dirty_flag_clear_same.
  }
  congruence.
  -   assert (Hold : R.is_side_dirty st observed = true).
  {
  destruct value; change (R.is_side_dirty (R.clear_side_dirty
        (R.with_queue (R.promote_controlled st target) (R.queue_remove target (R.queue st))) target) observed = true) in Hd;
        rewrite SC.dirty_flag_clear_other in Hd by exact Hneq; exact Hd.
  }
  rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (@dirty_finish_metadata st target value)))))).
  apply queue_remove_other; [congruence|exact (H observed Hold)].
Qed.

Lemma dirty_queued_get st fr target next next_fr value :
  R.complete_get st fr target = (next,next_fr,value) -> dirty_queued st -> dirty_queued next.
Proof.
  intros E H; apply (@dirty_queued_fields st next (@get_dirty_map _ _ _ _ _ _ E)); [|exact H].
  unfold R.complete_get,R.materialize in E; destruct (M.lookup _ _); inversion E; subst; destruct (R.rank_lt _ _ _); reflexivity.
Qed.

Lemma dirty_queued_dirty_get tf st fr target next next_fr value :
  R.dirty_complete_get tf st fr target = (next,next_fr,value) -> dirty_queued st -> dirty_queued next.
Proof.
  unfold R.dirty_complete_get; intros E H.
  set (prepared := R.materialize (if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) target) in *.
  assert (Hp : dirty_queued prepared).
  {
  apply (@dirty_queued_fields st prepared); [| |exact H].
  all: unfold prepared,R.materialize; destruct (M.lookup _ _);
  destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
  }
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:Er; inversion E; subst.
  -   destruct (@dirty_read_result tf prepared (R.frame_owner fr) target s Er)
      as [direct [written [_ [_ [-> _]]]]].
  exact (@dirty_queued_finish prepared target written Hp).
  -   exact Hp.
Qed.

Lemma dirty_queued_write st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) -> dirty_queued st -> dirty_queued next.
Proof.
  intros E H; apply (@dirty_queued_fields st next (@side_write_dirty_map _ _ _ _ _ _ E)); [|exact H].
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (@side_write_metadata _ _ _ _ _ _ E)))))).
Qed.

Lemma dirty_queued_commit st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) -> dirty_queued st -> dirty_queued next.
Proof.
  intros E H; apply (@dirty_queued_grows st next (@commit_dirty_map _ _ _ _ _ E)); [|exact H].
  apply set_value_cases in E as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; try auto.
  intros target Hin; apply publication_members; now left.
Qed.

Lemma dirty_queued_enqueue_mark st written : dirty_queued st ->
  dirty_queued (R.enqueue (R.mark_side_dirty st written) written).
Proof.
  intros H target Hd; apply queue_insert_members; destruct (V.eq_dec target written) as [->|Hneq]; [now left|].
  right; change (R.is_side_dirty (R.mark_side_dirty st written) target = true) in Hd.
  rewrite SC.dirty_flag_mark_other in Hd by exact Hneq; exact (H target Hd).
Qed.

Lemma dirty_queued_after_start tf st owner k after :
  dirty_scheduled (configuration st (R.StartEpisode owner k)) ->
  Sem.step tf (configuration st (R.StartEpisode owner k)) after -> dirty_scheduled after.
Proof.
  intros H E; unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control] in E.
  inversion E; subst; intros target Hd; cbn [R.cfg_state R.cfg_control] in Hd |- *.
  destruct (V.eq_dec target owner) as [->|Hneq].
  -   rewrite SC.dirty_flag_clear_same in Hd; discriminate.
  -   rewrite SC.dirty_flag_clear_other in Hd by exact Hneq.
  assert (Hold : R.is_side_dirty st target = true).
  {
  unfold R.materialize in Hd; destruct (M.lookup _ _); exact Hd.
  }
  destruct (H target Hold) as [Hqueue|[other Hbad]].
  +   left; change (In target (R.queue (R.materialize st owner))); unfold R.materialize; destruct (M.lookup _ _); exact Hqueue.
  +   change (R.StartEpisode owner k = R.StartEpisode target other) in Hbad; inversion Hbad; congruence.
Qed.

Definition dirty_except st written := forall target, R.is_side_dirty st target = true ->
  In target (R.queue st) \/ target = written.
Lemma dirty_except_queued st written : dirty_queued st -> dirty_except st written.
Proof.
  intros H target Hd; left; exact (H target Hd).
Qed.

Lemma dirty_except_mark st written : dirty_queued st -> dirty_except (R.mark_side_dirty st written) written.
Proof.
  intros H target Hd; destruct (V.eq_dec target written) as [->|Hneq]; [now right|].
  left; rewrite SC.dirty_flag_mark_other in Hd by exact Hneq; exact (H target Hd).
Qed.

Lemma dirty_except_pop st head tail : R.queue st = head :: tail -> dirty_queued st ->
  dirty_except (R.with_queue st tail) head.
Proof.
  intros Hqueue H target Hd; change (R.is_side_dirty st target = true) in Hd.
  pose proof (H target Hd) as Hin; rewrite Hqueue in Hin; destruct Hin as [<-|Hin]; [now right|now left].
Qed.

Lemma dirty_except_clear st written : dirty_except st written -> dirty_queued (R.clear_side_dirty st written).
Proof.
  intros H target Hd; destruct (V.eq_dec target written) as [->|Hneq].
  -   rewrite SC.dirty_flag_clear_same in Hd; discriminate.
  -   rewrite SC.dirty_flag_clear_other in Hd by exact Hneq.
  destruct (H target Hd) as [Hin|Heq]; [exact Hin|congruence].
Qed.

Lemma dirty_queued_scheduled st ctrl : dirty_queued st -> dirty_scheduled (configuration st ctrl).
Proof.
  intros H target Hd; left; exact (H target Hd).
Qed.

Lemma dirty_except_scheduled st owner k : dirty_except st owner ->
  dirty_scheduled (configuration st (R.StartEpisode owner k)).
Proof.
  intros H target Hd; destruct (H target Hd) as [Hin|Heq]; [now left|].
  subst target; right; exists k; reflexivity.
Qed.

Lemma dirty_scheduled_not_starting st ctrl :
  (forall owner k, ctrl <> R.StartEpisode owner k) ->
  dirty_scheduled (configuration st ctrl) -> dirty_queued st.
Proof.
  intros Houtside H target Hd; destruct (H target Hd) as [Hin|[k Hbad]]; [exact Hin|].
  exfalso; apply (Houtside target k); exact Hbad.
Qed.

Lemma dirty_queued_materialize st target : dirty_queued st -> dirty_queued (R.materialize st target).
Proof.
  intro H; unfold R.materialize; destruct (M.lookup _ _); exact H.
Qed.

Lemma dirty_queued_observe st target : dirty_queued st -> dirty_queued (R.observe st target).
Proof.
  intro H; unfold R.observe; destruct (Ranks.observe _ _); exact H.
Qed.

Lemma dirty_queued_enqueue st target : dirty_queued st -> dirty_queued (R.enqueue st target).
Proof.
  intros H other Hd; apply queue_insert_members; right; exact (H other Hd).
Qed.

Lemma dirty_queued_flush st : dirty_queued st -> dirty_queued (R.flush_deferred st).
Proof.
  intros H target Hd; apply queue_many_members; right; exact (H target Hd).
Qed.

Lemma dirty_queued_request st target : dirty_queued st -> dirty_queued (R.request_spawn st target).
Proof.
  intro H; unfold R.request_spawn; destruct (S.mem _ _); exact H.
Qed.

Lemma dirty_queued_reset st target : dirty_queued st -> dirty_queued (R.reset_registered_cells st target).
Proof.
  intro H; unfold R.reset_registered_cells; destruct Features.restart_side_phases; exact H.
Qed.

Ltac dirty_queued_administration H :=
  first [exact H|apply dirty_queued_materialize; dirty_queued_administration H|
    apply dirty_queued_observe; dirty_queued_administration H|
    apply dirty_queued_clear; dirty_queued_administration H|
    apply dirty_queued_enqueue; dirty_queued_administration H|
    apply dirty_queued_flush; dirty_queued_administration H|
    apply dirty_queued_request; dirty_queued_administration H|
    apply dirty_queued_reset; dirty_queued_administration H|
    match goal with Eg : R.complete_get ?base ?fr ?target = (?next,?next_fr,?value) |- dirty_queued ?next =>
      eapply dirty_queued_get; [exact Eg|dirty_queued_administration H] end|
    match goal with Eg : R.dirty_complete_get ?tf ?base ?fr ?target = (?next,?next_fr,?value) |- dirty_queued ?next =>
      eapply dirty_queued_dirty_get; [exact Eg|dirty_queued_administration H] end|
    match goal with Ew : R.write_side_contribution ?base ?fr ?target ?input = (?next,?changed) |- dirty_queued ?next =>
      eapply dirty_queued_write; [exact Ew|dirty_queued_administration H] end|
    match goal with Es : R.set_value ?base ?fr ?input = (?next,?next_fr) |- dirty_queued ?next =>
      eapply dirty_queued_commit; [exact Es|dirty_queued_administration H] end|
    match goal with |- dirty_queued (R.enqueue (R.mark_side_dirty ?base ?target) ?target) =>
      apply dirty_queued_enqueue_mark; dirty_queued_administration H end|
    match goal with Eq : R.queue ?base = ?head :: ?tail |-
      dirty_queued (R.clear_side_dirty (R.with_queue ?base ?tail) ?head) =>
      apply dirty_except_clear; eapply dirty_except_pop; [exact Eq|dirty_queued_administration H] end|
    match goal with |- dirty_queued (R.add_reader ?base ?target ?reader) =>
      change (dirty_queued base); dirty_queued_administration H end|
    match goal with |- dirty_queued (R.publish_targets ?base ?fr) =>
      change (dirty_queued base); dirty_queued_administration H end|
    match goal with |- dirty_queued (R.remember_dormant ?base ?target) =>
      change (dirty_queued base); dirty_queued_administration H end|
    match goal with |- dirty_queued (if ?test then _ else _) =>
      destruct test; dirty_queued_administration H end].
Ltac dirty_schedule_administration H :=
  first [apply dirty_queued_scheduled; dirty_queued_administration H|
    apply dirty_except_scheduled;
      first [apply dirty_except_mark; dirty_queued_administration H|
        eapply dirty_except_pop; [eassumption|dirty_queued_administration H]]].
Lemma dirty_schedule_step tf before after :
  dirty_scheduled before -> Sem.step tf before after -> dirty_scheduled after.
Proof.
  destruct before as [st ctrl]; destruct ctrl as [|seeds|remaining|owner k|fr body k|fr direct pending k|fr direct k|fr k|k];
    intros Hscheduled E;
    try solve [eapply dirty_queued_after_start; eassumption].
  all: assert (Hqueued : dirty_queued st) by
  (eapply dirty_scheduled_not_starting; [|exact Hscheduled]; intros target boundary Hbad; discriminate Hbad).
  all: unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control] in E.
  -   inspect_machine_step E; try discriminate; inversion E; subst; dirty_schedule_administration Hqueued.
  -   destruct seeds; inspect_machine_step E; try discriminate; inversion E; subst; dirty_schedule_administration Hqueued.
  -   inspect_machine_step E; try discriminate; inversion E; subst; dirty_schedule_administration Hqueued.
  -   destruct body; repeat match type of E with context [match Ranks.lookup ?order ?target with _ => _ end] =>
      destruct (Ranks.lookup order target) eqn:? end;
      inspect_machine_step E; try discriminate; inversion E; subst; dirty_schedule_administration Hqueued.
  -   destruct pending; inspect_machine_step E; try discriminate; inversion E; subst; dirty_schedule_administration Hqueued.
  -   inspect_machine_step E; try discriminate; inversion E; subst; dirty_schedule_administration Hqueued.
  -   inspect_machine_step E; try discriminate; inversion E; subst; dirty_schedule_administration Hqueued.
  -   destruct k; inspect_machine_step E; try discriminate; inversion E; subst; dirty_schedule_administration Hqueued.
Qed.

Theorem reachable_dirty_scheduled tf roots c :
  Sem.steps tf (R.initial_config roots) c -> dirty_scheduled c.
Proof.
  assert (Hwalk : forall first last, Sem.steps tf first last ->
    dirty_scheduled first -> dirty_scheduled last).
  {
  intros first last H; induction H; intro Hdirty; [exact Hdirty|apply IHsteps; eapply dirty_schedule_step; eassumption].
  }
  intro Hr; apply (Hwalk _ _ Hr); intros target Hd.
  change (R.is_side_dirty R.empty_state target = true) in Hd.
  unfold R.is_side_dirty in Hd; cbn in Hd; rewrite ML.lookup_empty in Hd; discriminate.
Qed.

Lemma scope_le_of_not_higher st owner target : RankLaws.valid (R.ranking st) ->
  ranked st owner -> ranked st target -> R.rank_lt st owner target = false ->
  scope_le st target owner.
Proof.
  intros Hvalid Howner Htarget Hlt.
  pose proof (proj1 (@compare_rank_false st owner target Howner Htarget) Hlt) as Hle.
  destruct (Nat.eq_dec (priority st target) (priority st owner)) as [Heq|Hneq].
  -   left; exact (@priority_distinct st target owner Hvalid Htarget Howner Heq).
  -   right; apply (proj2 (@compare_rank st target owner Htarget Howner)); lia.
Qed.

(** Higher dirty targets would already be queued. A lower dirty read
    would strictly spend protected potential. Both are excluded in a
    round whose relevant credits stay equal. *)
Theorem quiet_dirty_get_no_flush sources tf st fr target next next_fr value :
  RankLaws.valid (R.ranking st) -> ranked st (R.frame_owner fr) -> ranked st target ->
  dirty_queued st -> queue_below st (R.frame_owner fr) ->
  R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  (forall observed, scope_le st observed (R.frame_owner fr) ->
    SC.dirty_potential sources next observed = SC.dirty_potential sources st observed) ->
  R.try_dirty_read tf
    (R.materialize (if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) target)
    (R.frame_owner fr) target = None.
Proof.
  intros Hvalid Howner Htarget Hscheduled Hbelow E Hcredits.
  set (prepared := R.materialize (if R.rank_lt st (R.frame_owner fr) target
    then st else R.promote_controlled st target) target).
  destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target) eqn:Er; [|reflexivity].
  exfalso; destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hhigher.
  -   assert (Hd : R.is_side_dirty st target = true).
  {
  pose proof (@dirty_read_is_dirty tf prepared (R.frame_owner fr) target s Er) as Hd.
  unfold prepared,R.materialize in Hd; destruct (M.lookup _ _); exact Hd.
  }
  pose proof (Hscheduled target Hd) as Hin.
  pose proof (proj1 (Forall_forall _ _) Hbelow target Hin) as Hlower.
  change (priority st target < priority st (R.frame_owner fr)) in Hlower.
  pose proof (proj1 (@compare_rank st (R.frame_owner fr) target Howner Htarget) Hhigher); lia.
  -   pose proof (Hcredits target (@scope_le_of_not_higher st (R.frame_owner fr) target
      Hvalid Howner Htarget Hhigher)) as Hsame.
  pose proof (@dirty_get_spends sources tf st fr target next next_fr value E
  ltac:(exists s; rewrite Hhigher; exact Er)); lia.
Qed.

Corollary quiet_dirty_get_layout sources tf st fr target next next_fr value :
  RankLaws.valid (R.ranking st) -> ranked st (R.frame_owner fr) -> ranked st target ->
  dirty_queued st -> queue_below st (R.frame_owner fr) ->
  R.dirty_complete_get tf st fr target = (next,next_fr,value) ->
  (forall observed, scope_le st observed (R.frame_owner fr) ->
    SC.dirty_potential sources next observed = SC.dirty_potential sources st observed) ->
  R.queue next = R.queue st /\ R.deferred_wakes next = R.deferred_wakes st /\
    (forall owner, R.sigma_value next owner = R.sigma_value st owner).
Proof.
  intros Hvalid Howner Htarget Hscheduled Hbelow E Hcredits.
  pose proof (@quiet_dirty_get_no_flush sources tf st fr target next next_fr value
    Hvalid Howner Htarget Hscheduled Hbelow E Hcredits) as Er.
  unfold R.dirty_complete_get in E; rewrite Er in E; inversion E; subst next.
  repeat split.
  -   unfold R.materialize; destruct (M.lookup _ _); destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
  -   unfold R.materialize; destruct (M.lookup _ _); destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
  -   intro owner; change (R.sigma_value (R.materialize
      (if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) target) owner =
      R.sigma_value st owner).
  rewrite materialize_valuation; destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
Qed.

Lemma equal_activation_no_new_materialization support tf first last target :
  Sem.steps tf first last -> activation_credit support (R.cfg_state last) =
    activation_credit support (R.cfg_state first) ->
  In target support -> R.is_materialized (R.cfg_state last) target = true ->
  R.is_materialized (R.cfg_state first) target = true.
Proof.
  intros H E Hin Hmat; rewrite <- (proj2 (@activation_credit_equal support tf first last H E target Hin)); exact Hmat.
Qed.

Lemma equal_activation_no_discovery support tf first last target :
  Sem.steps tf first last -> activation_credit support (R.cfg_state last) =
    activation_credit support (R.cfg_state first) ->
  In target support -> ranked (R.cfg_state last) target -> ranked (R.cfg_state first) target.
Proof.
  intros H E Hin [n Hrank]; exists n; rewrite <- (proj1 (@activation_credit_equal support tf first last H E target Hin)); exact Hrank.
Qed.

Lemma equal_source_credit_write targets st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  In target targets ->
  SC.source_credit targets next (R.frame_owner fr) =
    SC.source_credit targets st (R.frame_owner fr) ->
  changed = false.
Proof.
  intros E Hin Hcredit; destruct changed; [|reflexivity].
  pose proof (@SC.source_credit_write_strict targets st fr target input next E Hin); lia.
Qed.

Lemma equal_activation_order support tf first last x y :
  Sem.steps tf first last ->
  activation_credit support (R.cfg_state last) = activation_credit support (R.cfg_state first) ->
  In x support -> In y support ->
  R.rank_lt (R.cfg_state last) x y = R.rank_lt (R.cfg_state first) x y.
Proof.
  intros H E Hx Hy; unfold R.rank_lt,R.ranking_lt.
  rewrite (proj1 (@activation_credit_equal support tf first last H E x Hx)),
    (proj1 (@activation_credit_equal support tf first last H E y Hy)); reflexivity.
Qed.

Lemma equal_activation_protected_targets support tf first last owner :
  Sem.steps tf first last ->
  activation_credit support (R.cfg_state last) = activation_credit support (R.cfg_state first) ->
  In owner support ->
  protected_targets support (R.cfg_state last) owner =
    protected_targets support (R.cfg_state first) owner.
Proof.
  intros H E Howner; unfold protected_targets; apply filter_ext_in.
  intros target Hin; destruct (V.eq_dec target owner); [reflexivity|].
  exact (@equal_activation_order support tf first last target owner H E Hin Howner).
Qed.

Theorem equal_round_budget_lower_potentials tf roots (finite : Sem.finite_system tf roots)
  owner first last first_fr last_fr :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  R.frame_owner first_fr = owner -> R.frame_owner last_fr = owner ->
  In owner (Sem.support finite) ->
  round_budget (Sem.support finite) (protected_targets (Sem.support finite) (R.cfg_state first) owner)
      (R.cfg_state last) last_fr =
    round_budget (Sem.support finite) (protected_targets (Sem.support finite) (R.cfg_state first) owner)
      (R.cfg_state first) first_fr ->
  forall target, In target (Sem.support finite) -> scope_le (R.cfg_state last) target owner ->
    SC.dirty_potential (Sem.support finite) (R.cfg_state last) target =
      SC.dirty_potential (Sem.support finite) (R.cfg_state first) target.
Proof.
  intros Hr H Hfirst Hlast Howner E target Hin Hscope.
  pose proof (f_equal (@fst nat (nat * nat)) E) as Eevaluation.
  pose proof (f_equal (fun vector : credit_vector => fst (snd vector)) E) as Edirty.
  change (evaluation_credit (Sem.support finite) (R.frame_owner last_fr) (R.cfg_state last) =
  evaluation_credit (Sem.support finite) (R.frame_owner first_fr) (R.cfg_state first)) in Eevaluation.
  change (dirty_budget (Sem.support finite) (protected_targets (Sem.support finite) (R.cfg_state first) owner)
  (R.cfg_state last) =
  dirty_budget (Sem.support finite) (protected_targets (Sem.support finite) (R.cfg_state first) owner)
  (R.cfg_state first)) in Edirty.
  rewrite Hfirst,Hlast in Eevaluation.
  pose proof (proj1 (@equal_evaluation_credit tf roots (Sem.support finite) owner first last Hr H Eevaluation)) as Eactivation.
  assert (Htarget : In target (protected_targets (Sem.support finite) (R.cfg_state first) owner)).
  {
  rewrite <- (@equal_activation_protected_targets (Sem.support finite) tf first last owner
      (@active_trace_path tf owner first last H) Eactivation Howner).
  apply protected_targets_spec; now split.
  }
  exact (@equal_dirty_budget tf roots finite owner
    (protected_targets (Sem.support finite) (R.cfg_state first) owner) first last
    Hr H (protected_targets_scoped _ _ _) Edirty target Htarget).
Qed.

Lemma credit_lt_irrefl budget : ~ credit_lt budget budget.
Proof.
  destruct budget as [evaluation [dirty ordinary]]; unfold credit_lt; cbn; intuition lia.
Qed.

Lemma credit_lt_after small middle large :
  credit_lt small middle -> (middle = large \/ credit_lt middle large) -> credit_lt small large.
Proof.
  intros H [->|Htail]; [exact H|eapply credit_lt_trans; eassumption].
Qed.

Lemma credit_lt_before small middle large :
  (small = middle \/ credit_lt small middle) -> credit_lt middle large -> credit_lt small large.
Proof.
  intros [->|Hhead] H; [exact H|eapply credit_lt_trans; eassumption].
Qed.

(** Payment survives the evaluation prefix and the entire drain suffix,
    including nested higher episodes and their scoped resets. *)
Theorem round_through_paid_commit tf roots (finite : Sem.finite_system tf roots)
  owner targets first first_fr committed commit_fr direct k next next_fr last last_fr :
  Sem.steps tf (R.initial_config roots) first ->
  active_trace tf owner first (configuration committed (R.RunCommit commit_fr direct k)) ->
  R.set_value (R.flush_deferred committed) commit_fr direct = (next,next_fr) ->
  active_trace tf owner (configuration next (R.RunDrain next_fr k)) last ->
  In first_fr (live_frames (R.cfg_control first)) -> R.frame_owner first_fr = owner ->
  R.frame_owner commit_fr = owner ->
  In last_fr (live_frames (R.cfg_control last)) -> R.frame_owner last_fr = owner ->
  Forall (fun target => scope_le (R.cfg_state first) target owner) targets -> In owner targets ->
  S.mem owner (R.controlled committed) = true ->
  ~ eqv (R.sigma_value next owner) (R.sigma_value committed owner) ->
  credit_lt (round_budget (Sem.support finite) targets (R.cfg_state last) last_fr)
    (round_budget (Sem.support finite) targets (R.cfg_state first) first_fr).
Proof.
  intros Hr Hprefix Eset Hsuffix Hfirst Hfirst_owner Hcommit_owner Hlast Hlast_owner Htargets Howner Hcontrolled Hchanged.
  assert (Hcommit : Sem.steps tf (R.initial_config roots)
    (configuration committed (R.RunCommit commit_fr direct k))) by
    (eapply path_join; [exact Hr|exact (@active_trace_path tf owner _ _ Hprefix)]).
  assert (E : Sem.step tf (configuration committed (R.RunCommit commit_fr direct k))
    (configuration next (R.RunDrain next_fr k))).
  {
  unfold Sem.step,R.next_config; cbn [configuration R.cfg_state R.cfg_control]; now rewrite Eset.
  }
  assert (Hnext : Sem.steps tf (R.initial_config roots) (configuration next (R.RunDrain next_fr k))) by
    (eapply path_extend; eassumption).
  assert (Hnext_owner : R.frame_owner next_fr = owner) by
    (rewrite (@set_value_owner _ _ _ _ _ Eset); exact Hcommit_owner).
  pose proof (@round_budget_path tf roots finite owner targets first
    (configuration committed (R.RunCommit commit_fr direct k)) first_fr commit_fr
    Hr Hprefix Hfirst Hfirst_owner ltac:(cbn; now left) Hcommit_owner Htargets Howner) as Hbefore.
  assert (Hnext_targets : Forall (fun target => scope_le next target owner) targets).
  {
  apply Forall_forall; intros target Hin.
  apply (@scope_le_extension (R.cfg_state first) next target owner).
  -   eapply rank_extension_trans; [exact (@path_rank_extension tf _ _ (@active_trace_path tf owner _ _ Hprefix))|exact (@step_rank_extension tf _ _ E)].
  -   exact (proj1 (Forall_forall _ _) Htargets target Hin).
  }
  pose proof (@round_budget_path tf roots finite owner targets
    (configuration next (R.RunDrain next_fr k)) last next_fr last_fr
    Hnext Hsuffix ltac:(cbn; now left) Hnext_owner Hlast Hlast_owner Hnext_targets Howner) as Hafter.
  pose proof (@paid_commit_spends (Sem.support finite) targets committed commit_fr direct next next_fr
    (@reachable_live_materialized tf roots _ Hcommit commit_fr ltac:(cbn; now left))
    Eset ltac:(now rewrite Hcommit_owner) ltac:(now rewrite Hcommit_owner)) as Hpaid.
  apply (@credit_lt_before _ (round_budget (Sem.support finite) targets next next_fr)); [exact Hafter|].
  apply (@credit_lt_after _ (round_budget (Sem.support finite) targets committed commit_fr)); [exact Hpaid|exact Hbefore].
Qed.

Lemma flush_empty_state st : R.deferred_wakes st = [] -> R.flush_deferred st = st.
Proof.
  intro H; unfold R.flush_deferred,R.enqueue_all; rewrite H; cbn [R.queue_insert_all].
  destruct st; cbn in H; subst; reflexivity.
Qed.
Lemma stable_commit_state st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) ->
  eqv (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) ->
  next = st.
Proof.
  intros E Hsame; apply set_value_cases in E as [[_ [-> _]]|[_ [_ [[_ ->]|[Hdifferent ->]]]]]; try reflexivity.
  rewrite publication_value in Hsame; apply equivalent_true in Hsame; congruence.
Qed.
Lemma equal_controlled_commit_state st fr direct next next_fr :
  R.set_value st fr direct = (next,next_fr) ->
  S.mem (R.frame_owner fr) (R.controlled st) = true ->
  ordinary_credit next next_fr = ordinary_credit st fr -> next = st.
Proof.
  intros E Hcontrolled Hcredit; apply (@stable_commit_state st fr direct next next_fr E).
  destruct (R.equivalent (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr))) eqn:Hsame.
  - now apply equivalent_true.
  - apply equivalent_false in Hsame.
    pose proof (@controlled_commit_ordinary_strict st fr direct next next_fr E Hcontrolled Hsame); lia.
Qed.
Theorem quiet_commit_queue tf roots st fr direct k next next_fr :
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunCommit fr direct k)) ->
  queue_below st (R.frame_owner fr) -> R.deferred_wakes st = [] ->
  R.set_value (R.flush_deferred st) fr direct = (next,next_fr) ->
  ordinary_credit next next_fr = ordinary_credit st fr ->
  queue_below next (R.frame_owner next_fr) /\ R.deferred_wakes next = [].
Proof.
  intros Hr Hbelow Hwakes E Hcredit; rewrite (@flush_empty_state st Hwakes) in E.
  split.
  - rewrite (@set_value_owner _ _ _ _ _ E).
    destruct (S.mem (R.frame_owner fr) (R.controlled st)) eqn:Hcontrolled.
    + rewrite (@equal_controlled_commit_state st fr direct next next_fr E Hcontrolled Hcredit); exact Hbelow.
    + pose proof (inv_shape (proj2 (@reachable_invariants tf roots _ Hr))) as Hshape.
      pose proof (@reachable_reader_orientation tf roots _ Hr) as Horientation.
      change (reader_orientation st) in Horientation.
      assert (Howner : ranked st (R.frame_owner fr)) by exact (Forall_inv (shape_stack_ranks Hshape)).
      apply set_value_cases in E as [[_ [-> _]]|[_ [_ [[_ ->]|[_ ->]]]]]; try exact Hbelow.
      unfold queue_below,queue_under; change (Forall
        (fun target => priority st target < priority st (R.frame_owner fr))
        (R.queue (commit_publication st (R.frame_owner fr)
          (snd (if S.mem (R.frame_owner fr) (R.controlled st)
            then U.update false (R.frame_owner fr) (R.frame_phase fr)
              (R.sigma_value st (R.frame_owner fr)) (D.join direct (R.aggregate st (R.frame_owner fr)))
            else (R.frame_phase fr,D.join direct (R.aggregate st (R.frame_owner fr)))))))).
      apply Forall_forall; intros target Hin; apply publication_members in Hin as [Hin|[Hin|[_ [Hbad _]]]].
      * exact (proj1 (Forall_forall _ _) Hbelow target Hin).
      * destruct (Horientation (R.frame_owner fr) target Hin) as [Hbad|[Hnone|Hlower]].
        -- congruence.
        -- destruct Howner as [n Hrank]; congruence.
        -- apply (proj1 (@compare_rank st target (R.frame_owner fr)
            (@shape_readers tf _ Hshape (R.frame_owner fr) target Hin) Howner)); exact Hlower.
      * congruence.
  - rewrite (proj1 (proj2 (proj2 (proj2 (@set_value_metadata st fr direct next next_fr E))))); exact Hwakes.
Qed.

(** Equal credits preserve a quiet round through reads, spawns and side maintenance. *)
Lemma reachable_exposed_support tf roots (finite : Sem.finite_system tf roots) c :
  Sem.steps tf (R.initial_config roots) c -> Forall (fun x => In x (Sem.support finite)) (exposed (R.cfg_control c)).
Proof.
  intro Hr; destruct (@reachable_support tf roots finite c Hr) as [Hrank Hschedule].
  exact (@exposed_supported tf roots (Sem.support finite) c (Sem.system_supported finite) Hrank Hschedule
    (proj2 (@reachable_invariants tf roots c Hr))).
Qed.

Lemma observe_ranked_state st target : ranked st target -> R.observe st target = st.
Proof.
  intros [n Hn]; unfold R.observe.
  pose proof (@RankLaws.observe_existing (R.ranking st) target n Hn) as E.
  change (Ranks.observe (R.ranking st) target = (R.ranking st,n)) in E.
  rewrite E; destruct st; reflexivity.
Qed.

Definition quiet_control owner boundary st ctrl :=
  match ctrl with
  | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k =>
      R.frame_owner fr = owner /\ k = boundary
  | R.StartEpisode child _ => R.is_materialized st child = false
  | _ => False
  end.
Definition quiet_round owner boundary c :=
  queue_below (R.cfg_state c) owner /\ R.deferred_wakes (R.cfg_state c) = [] /\
    quiet_control owner boundary (R.cfg_state c) (R.cfg_control c).
Lemma quiet_get_step tf roots (finite : Sem.finite_system tf roots) st fr target tail k after :
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) ->
  Sem.step tf (configuration st (R.RunRhs fr (Syntax.Get target tail) k)) after ->
  queue_below st (R.frame_owner fr) -> R.deferred_wakes st = [] ->
  activation_credit (Sem.support finite) (R.cfg_state after) = activation_credit (Sem.support finite) st ->
  (forall observed, In observed (Sem.support finite) -> scope_le (R.cfg_state after) observed (R.frame_owner fr) ->
    SC.dirty_potential (Sem.support finite) (R.cfg_state after) observed = SC.dirty_potential (Sem.support finite) st observed) ->
  quiet_round (R.frame_owner fr) k after.
Proof.
  intros Hr E Hbelow Hwakes Ha Hd.
  pose proof (@reachable_exposed_support tf roots finite _ Hr) as Htarget.
  change (Forall (fun x => In x (Sem.support finite)) [target]) in Htarget.
  apply Forall_inv in Htarget.
  pose proof (@activation_credit_equal (Sem.support finite) tf _ after
    ltac:(eapply Sem.StepsStep; [exact E|constructor]) Ha target Htarget) as [Hrank Hmat].
  change (Ranks.lookup (R.ranking (R.cfg_state after)) target = Ranks.lookup (R.ranking st) target) in Hrank.
  change (R.is_materialized (R.cfg_state after) target = R.is_materialized st target) in Hmat.
  pose proof (inv_shape (proj2 (@reachable_invariants tf roots _ Hr))) as Hshape.
  unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control Syntax.Get] in E.
  destruct (R.is_dormant st target) eqn:Edormant.
  - inversion E; subst after; unfold quiet_round; cbn; repeat split; assumption || reflexivity.
  - destruct (Ranks.lookup (R.ranking st) target) as [n|] eqn:Erank.
    + rewrite (@observe_ranked_state st target ltac:(exists n; exact Erank)) in E.
      destruct (R.is_materialized st target) eqn:Emat.
      * destruct (R.dirty_complete_get tf st fr target) as [[next next_fr] value] eqn:Eget.
        inversion E; subst after.
        pose proof (@dirty_get_frame_owner tf st fr target next next_fr value Eget) as Howner.
        assert (Hqueued : dirty_queued st).
        {
          eapply dirty_scheduled_not_starting; [|exact (@reachable_dirty_scheduled tf roots _ Hr)]; intros; discriminate.
        }
        assert (Hsame : forall observed, scope_le st observed (R.frame_owner fr) ->
          SC.dirty_potential (Sem.support finite) next observed = SC.dirty_potential (Sem.support finite) st observed).
        {
          intros observed Hscope; apply Hd.
          - apply (proj1 (@reachable_support tf roots finite _ Hr)).
            destruct Hscope as [->|Hlt]; [exact (Forall_inv (shape_stack_ranks Hshape))|exact (proj1 (@rank_lt_ranked st _ _ Hlt))].
          - exact (@scope_le_extension st next observed (R.frame_owner fr) ltac:(unfold rank_extension; intros x rank Hx; rewrite (@dirty_get_ranking _ _ _ _ _ _ _ Eget); exact Hx) Hscope).
        }
        destruct (@quiet_dirty_get_layout (Sem.support finite) tf st fr target next next_fr value
          (shape_ranks Hshape) (Forall_inv (shape_stack_ranks Hshape)) ltac:(exists n; exact Erank)
          Hqueued Hbelow Eget Hsame) as [Hq [Hw Hv]].
        unfold quiet_round; cbn; split.
        {
          eapply queue_below_fields; [exact (@dirty_get_ranking _ _ _ _ _ _ _ Eget)|exact Hq|exact Hbelow].
        }
        split; [now rewrite Hw|split; [exact Howner|reflexivity]].
      * destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hhigher.
        -- inversion E; subst after; unfold quiet_round; cbn; repeat split; assumption.
        -- destruct (R.complete_get (R.enqueue st target) fr target) as [[next next_fr] value] eqn:Eget.
          inversion E; subst after; exfalso.
          unfold R.complete_get in Eget; inversion Eget; subst next.
          cbn [R.cfg_state] in Hmat.
          rewrite materialize_is_materialized in Hmat; discriminate.
    + destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)) eqn:Hpure.
      * inversion E; subst after; unfold quiet_round; cbn; repeat split; assumption || reflexivity.
      * inspect_machine_step E; inversion E; subst after; cbn [R.cfg_state] in Hrank.
        all: exfalso; try rewrite Hrank_get in Hrank.
        all: try (destruct (R.is_materialized (R.observe st target) target); change (Ranks.lookup (R.ranking (R.observe st target)) target = None) in Hrank).
        all: destruct (@observe_ranks st target) as [m Hm]; congruence.
Qed.

Lemma quiet_spawn_step tf roots (finite : Sem.finite_system tf roots) st fr target tail k after :
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) ->
  Sem.step tf (configuration st (R.RunRhs fr (Syntax.Spawn target tail) k)) after ->
  queue_below st (R.frame_owner fr) -> R.deferred_wakes st = [] ->
  activation_credit (Sem.support finite) (R.cfg_state after) = activation_credit (Sem.support finite) st ->
  quiet_round (R.frame_owner fr) k after.
Proof.
  intros Hr E Hbelow Hwakes Ha.
  pose proof (@reachable_exposed_support tf roots finite _ Hr) as Htarget.
  change (Forall (fun x => In x (Sem.support finite)) [target]) in Htarget; apply Forall_inv in Htarget.
  pose proof (@activation_credit_equal (Sem.support finite) tf _ after
    ltac:(eapply Sem.StepsStep; [exact E|constructor]) Ha target Htarget) as [Hrank Hmat].
  change (Ranks.lookup (R.ranking (R.cfg_state after)) target = Ranks.lookup (R.ranking st) target) in Hrank.
  change (R.is_materialized (R.cfg_state after) target = R.is_materialized st target) in Hmat.
  unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control Syntax.Spawn] in E.
  destruct Features.defer_spawns eqn:Hdefer.
  - inversion E; subst after; unfold quiet_round; cbn; split.
    + eapply queue_below_fields; [apply request_ranking| |exact Hbelow].
      unfold R.request_spawn; destruct (S.mem _ _); reflexivity.
    + split; [unfold R.request_spawn; destruct (S.mem _ _); exact Hwakes|now split].
  - destruct (R.is_dormant st target) eqn:Edormant.
    + inversion E; subst after; unfold quiet_round; cbn; repeat split; assumption || reflexivity.
    + destruct (Ranks.lookup (R.ranking st) target) as [n|] eqn:Erank.
      * rewrite (@observe_ranked_state st target ltac:(exists n; exact Erank)) in E.
        destruct (R.is_materialized st target) eqn:Emat.
        -- inversion E; subst after; unfold quiet_round; cbn; repeat split; assumption || reflexivity.
        -- destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hhigher.
          ++ inversion E; subst after; unfold quiet_round; cbn; repeat split; assumption.
          ++ inversion E; subst after; cbn [R.cfg_state] in Hmat.
            rewrite materialize_is_materialized in Hmat; discriminate.
      * destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target)) eqn:Hpure.
        -- inversion E; subst after; unfold quiet_round; cbn; repeat split; assumption || reflexivity.
        -- inspect_machine_step E; inversion E; subst after; cbn [R.cfg_state] in Hrank.
          all: exfalso; try rewrite materialize_ranking in Hrank.
          all: change (Ranks.lookup (R.ranking (R.observe st target)) target = None) in Hrank.
          all: destruct (@observe_ranks st target) as [m Hm]; congruence.
Qed.

Lemma cell_view_continue_side st fr target body k changed :
  cell_view st (R.cfg_state (R.continue_side st fr target body k changed)).
Proof.
  unfold R.continue_side; destruct changed; [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|];
    cbn; try (unfold R.materialize; destruct (M.lookup _ _)); split; reflexivity.
Qed.

Lemma cell_view_continue_dead st fr direct target pending k changed :
  cell_view st (R.cfg_state (R.continue_dead st fr direct target pending k changed)).
Proof.
  unfold R.continue_dead; destruct changed; [destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))|];
    cbn; try (unfold R.materialize; destruct (M.lookup _ _)); split; reflexivity.
Qed.

Lemma quiet_side_step tf roots (finite : Sem.finite_system tf roots) st fr target raw tail k after :
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) ->
  Sem.step tf (configuration st (R.RunRhs fr (Syntax.Side target raw tail) k)) after ->
  queue_below st (R.frame_owner fr) -> R.deferred_wakes st = [] ->
  activation_credit (Sem.support finite) (R.cfg_state after) = activation_credit (Sem.support finite) st ->
  SC.source_credit (Sem.support finite) (R.cfg_state after) (R.frame_owner fr) =
    SC.source_credit (Sem.support finite) st (R.frame_owner fr) ->
  quiet_round (R.frame_owner fr) k after.
Proof.
  intros Hr E Hbelow Hwakes Ha Hs.
  pose proof (@reachable_exposed_support tf roots finite _ Hr) as Htarget.
  change (Forall (fun x => In x (Sem.support finite)) [target]) in Htarget; apply Forall_inv in Htarget.
  pose proof (@activation_credit_equal (Sem.support finite) tf _ after
    ltac:(eapply Sem.StepsStep; [exact E|constructor]) Ha target Htarget) as [Hrank Hmat].
  change (Ranks.lookup (R.ranking (R.cfg_state after)) target = Ranks.lookup (R.ranking st) target) in Hrank.
  unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control Syntax.Side R.record_side_input] in E.
  destruct (R.write_side_contribution (R.observe st target)
    (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) target
    (R.accumulated_side_input fr target raw)) as [next changed] eqn:Ewrite.
  assert (Hlayout : R.ranking (R.cfg_state after) = R.ranking next /\
    cell_view next (R.cfg_state after)).
  {
    destruct (R.is_dormant st target),changed; inversion E; subst after;
      unfold R.continue_side; decompose_operation; cbn; repeat split; reflexivity.
  }
  destruct Hlayout as [Hranks Hview].
  rewrite Hranks,(proj1 (proj2 (@side_write_metadata _ _ _ _ _ _ Ewrite))) in Hrank.
  destruct (@observe_ranks st target) as [n Hn].
  assert (Hknown : ranked st target) by (exists n; now rewrite <- Hrank).
  rewrite (@observe_ranked_state st target Hknown) in Ewrite,Hrank.
  assert (Edormant : R.is_dormant st target = false).
  {
    destruct Hknown as [m Hm]; unfold R.is_dormant; rewrite Hm.
    rewrite !andb_false_r; reflexivity.
  }
  assert (Hsame : SC.source_credit (Sem.support finite) next (R.frame_owner fr) =
    SC.source_credit (Sem.support finite) st (R.frame_owner fr)).
  {
    rewrite <- (@source_credit_view (Sem.support finite) next (R.cfg_state after) (R.frame_owner fr) Hview); exact Hs.
  }
  assert (Hchanged : changed = false).
  {
    eapply equal_source_credit_write; [exact Ewrite|exact Htarget|exact Hsame].
  }
  rewrite Edormant,Hchanged in E; inversion E; subst after.
  unfold R.continue_side,quiet_round; cbn; split.
  - eapply queue_below_fields; [exact (proj1 (proj2 (@side_write_metadata _ _ _ _ _ _ Ewrite)))|
      exact (proj1 (proj2 (proj2 (proj2 (proj2 (@side_write_metadata _ _ _ _ _ _ Ewrite))))))|exact Hbelow].
  - split; [rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (@side_write_metadata _ _ _ _ _ _ Ewrite))))))); exact Hwakes|now split].
Qed.

Lemma quiet_dead_step tf roots (finite : Sem.finite_system tf roots) st fr direct pending k after :
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunDead fr direct pending k)) ->
  Sem.step tf (configuration st (R.RunDead fr direct pending k)) after ->
  queue_below st (R.frame_owner fr) -> R.deferred_wakes st = [] ->
  SC.source_credit (Sem.support finite) (R.cfg_state after) (R.frame_owner fr) =
    SC.source_credit (Sem.support finite) st (R.frame_owner fr) ->
  quiet_round (R.frame_owner fr) k after.
Proof.
  intros Hr E Hbelow Hwakes Hs.
  unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control] in E.
  destruct pending as [|target rest].
  - inversion E; subst after; unfold quiet_round; cbn; repeat split; assumption || reflexivity.
  - destruct (S.mem target (R.frame_current_targets fr)) eqn:Hcurrent.
    + inversion E; subst after; unfold quiet_round; cbn; repeat split; assumption || reflexivity.
    + destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Ewrite.
      assert (Hview : cell_view next (R.cfg_state after)).
      {
        destruct changed; inversion E; subst after; unfold R.continue_dead;
          decompose_operation; cbn; split; reflexivity.
      }
      assert (Htarget : In target (Sem.support finite)).
      {
        apply (proj1 (@reachable_support tf roots finite _ Hr)).
        pose proof (proj1 (@reachable_invariants tf roots _ Hr)) as Hknown.
        change (targets_known st /\ frame_known st fr /\ ranked_list st (target::rest) /\ continuation_known st k) in Hknown.
        exact (Forall_inv (proj1 (proj2 (proj2 Hknown)))).
      }
      assert (Hchanged : changed = false).
      {
        eapply equal_source_credit_write; [exact Ewrite|exact Htarget|].
        rewrite <- (@source_credit_view (Sem.support finite) next (R.cfg_state after) (R.frame_owner fr) Hview); exact Hs.
      }
      rewrite Hchanged in E; inversion E; subst after.
      unfold R.continue_dead,quiet_round; cbn; split.
      * eapply queue_below_fields; [exact (proj1 (proj2 (@side_write_metadata _ _ _ _ _ _ Ewrite)))|
          exact (proj1 (proj2 (proj2 (proj2 (proj2 (@side_write_metadata _ _ _ _ _ _ Ewrite))))))|exact Hbelow].
      * split; [rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (@side_write_metadata _ _ _ _ _ _ Ewrite))))))); exact Hwakes|now split].
Qed.

Lemma credit_between_equal first middle last :
  (middle = first \/ credit_lt middle first) ->
  (last = middle \/ credit_lt last middle) ->
  last = first -> middle = first.
Proof.
  intros Hhead Htail E; subst last; destruct Hhead as [E|Hhead]; [exact E|].
  exfalso; destruct Htail as [E|Htail].
  - subst middle; exact (@credit_lt_irrefl first Hhead).
  - exact (@credit_lt_irrefl first (@credit_lt_trans first middle first Htail Hhead)).
Qed.

Theorem equal_round_budget_split tf roots (finite : Sem.finite_system tf roots)
  owner targets first middle last first_fr middle_fr last_fr :
  Sem.steps tf (R.initial_config roots) first ->
  active_trace tf owner first middle -> active_trace tf owner middle last ->
  In first_fr (live_frames (R.cfg_control first)) -> R.frame_owner first_fr = owner ->
  In middle_fr (live_frames (R.cfg_control middle)) -> R.frame_owner middle_fr = owner ->
  In last_fr (live_frames (R.cfg_control last)) -> R.frame_owner last_fr = owner ->
  Forall (fun target => scope_le (R.cfg_state first) target owner) targets -> In owner targets ->
  round_budget (Sem.support finite) targets (R.cfg_state last) last_fr =
    round_budget (Sem.support finite) targets (R.cfg_state first) first_fr ->
  round_budget (Sem.support finite) targets (R.cfg_state middle) middle_fr =
    round_budget (Sem.support finite) targets (R.cfg_state first) first_fr.
Proof.
  intros Hr Hprefix Hsuffix Hfirst Hofirst Hmiddle Homiddle Hlast Holast Hscope Hin E.
  eapply credit_between_equal; [| |exact E].
  - exact (@round_budget_path tf roots finite owner targets first middle first_fr middle_fr
      Hr Hprefix Hfirst Hofirst Hmiddle Homiddle Hscope Hin).
  - eapply (@round_budget_path tf roots finite owner targets middle last middle_fr last_fr).
    + eapply path_join; [exact Hr|exact (@active_trace_path tf owner first middle Hprefix)].
    + exact Hsuffix.
    + exact Hmiddle.
    + exact Homiddle.
    + exact Hlast.
    + exact Holast.
    + apply Forall_forall; intros target Htarget; eapply scope_le_extension.
      * exact (@path_rank_extension tf first middle (@active_trace_path tf owner first middle Hprefix)).
      * exact (proj1 (Forall_forall _ _) Hscope target Htarget).
    + exact Hin.
Qed.

Lemma quiet_start_impossible tf roots (finite : Sem.finite_system tf roots) st child k after :
  Sem.steps tf (R.initial_config roots) (configuration st (R.StartEpisode child k)) ->
  Sem.step tf (configuration st (R.StartEpisode child k)) after ->
  R.is_materialized st child = false ->
  activation_credit (Sem.support finite) (R.cfg_state after) = activation_credit (Sem.support finite) st ->
  False.
Proof.
  intros Hr E Hmat Ha.
  pose proof (@active_supported tf roots finite _ child Hr ltac:(cbn; now left)) as Hin.
  pose proof (proj2 (@activation_credit_equal (Sem.support finite) tf _ after
    ltac:(eapply Sem.StepsStep; [exact E|constructor]) Ha child Hin)) as Hsame.
  unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control] in E; inversion E; subst after.
  change (R.is_materialized (R.materialize st child) child = R.is_materialized st child) in Hsame.
  rewrite materialize_is_materialized,Hmat in Hsame; discriminate.
Qed.


Lemma quiet_drain_returns tf roots st fr k after :
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunDrain fr k)) ->
  Sem.step tf (configuration st (R.RunDrain fr k)) after ->
  queue_below st (R.frame_owner fr) -> R.cfg_control after = R.Return k.
Proof.
  intros Hr E Hbelow; pose proof (inv_shape (proj2 (@reachable_invariants tf roots _ Hr))) as Hshape.
  unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control] in E.
  destruct (R.queue st) as [|head rest] eqn:Hqueue; cbn [R.queue_peek R.queue_pop] in E.
  - inversion E; reflexivity.
  - pose proof Hbelow as Hsmall; unfold queue_below,queue_under in Hsmall; rewrite Hqueue in Hsmall; apply Forall_inv in Hsmall.
    destruct (V.eq_dec head (R.frame_owner fr)) as [Heq|Hneq]; [subst head; lia|].
    assert (Hlower : R.rank_lt st (R.frame_owner fr) head = false).
    {
      destruct (R.rank_lt st (R.frame_owner fr) head) eqn:Hlt; [|reflexivity].
      destruct (@rank_lt_ranked st _ _ Hlt) as [Howner Hhead].
      pose proof (proj1 (@compare_rank st (R.frame_owner fr) head Howner Hhead) Hlt); lia.
    }
    rewrite Hlower in E; inversion E; reflexivity.
Qed.

Theorem quiet_round_step tf roots (finite : Sem.finite_system tf roots) owner boundary first next first_fr next_fr :
  Sem.steps tf (R.initial_config roots) first -> Sem.step tf first next ->
  In owner (active_owners (R.cfg_control next)) ->
  In first_fr (live_frames (R.cfg_control first)) -> R.frame_owner first_fr = owner ->
  In next_fr (live_frames (R.cfg_control next)) -> R.frame_owner next_fr = owner ->
  activation_credit (Sem.support finite) (R.cfg_state next) = activation_credit (Sem.support finite) (R.cfg_state first) ->
  SC.source_credit (Sem.support finite) (R.cfg_state next) owner = SC.source_credit (Sem.support finite) (R.cfg_state first) owner ->
  ordinary_credit (R.cfg_state next) next_fr = ordinary_credit (R.cfg_state first) first_fr ->
  (forall observed, In observed (Sem.support finite) -> scope_le (R.cfg_state next) observed owner ->
    SC.dirty_potential (Sem.support finite) (R.cfg_state next) observed =
      SC.dirty_potential (Sem.support finite) (R.cfg_state first) observed) ->
  quiet_round owner boundary first -> quiet_round owner boundary next.
Proof.
  intros Hr E Hactive Hfirst Hofirst Hnext Honext Ha Hs Ho Hd [Hbelow [Hwakes Hquiet]].
  pose proof (inv_shape (proj2 (@reachable_invariants tf roots first Hr))) as Hshape.
  destruct first as [st ctrl]; destruct ctrl as [|seeds|remaining|child k|fr body k|fr direct pending k|fr direct k|fr k|k];
    cbn [R.cfg_state R.cfg_control quiet_control] in Hquiet; try contradiction.
  - exfalso; exact (@quiet_start_impossible tf roots finite st child k next Hr E Hquiet Ha).
  - destruct Hquiet as [Howner ->]; rewrite <- Howner in Hbelow,Hs,Hd; cbn [R.cfg_state] in Ha,Hwakes.
    rewrite <- Howner; destruct body as [direct|target tail|target raw tail|target tail].
    + unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control Syntax.Ret] in E.
      inversion E; subst next; unfold quiet_round; cbn; repeat split; assumption || reflexivity.
    + exact (@quiet_get_step tf roots finite st fr target tail boundary next Hr E Hbelow Hwakes Ha Hd).
    + exact (@quiet_side_step tf roots finite st fr target raw tail boundary next Hr E Hbelow Hwakes Ha Hs).
    + exact (@quiet_spawn_step tf roots finite st fr target tail boundary next Hr E Hbelow Hwakes Ha).
  - destruct Hquiet as [Howner ->]; rewrite <- Howner in Hbelow,Hs; cbn [R.cfg_state] in Hwakes.
    rewrite <- Howner; exact (@quiet_dead_step tf roots finite st fr direct pending boundary next Hr E Hbelow Hwakes Hs).
  - destruct Hquiet as [Howner ->].
    assert (Hfirst_eq : first_fr = fr).
    {
      exact (@live_frame_unique tf _ first_fr fr Hshape Hfirst ltac:(cbn; now left) ltac:(congruence)).
    }
    subst first_fr.
    unfold Sem.step,R.next_config in E; cbn [configuration R.cfg_state R.cfg_control] in E.
    destruct (R.set_value (R.flush_deferred st) fr direct) as [after after_fr] eqn:Eset.
    inversion E; subst next.
    assert (Hafter : Sem.steps tf (R.initial_config roots) (configuration after (R.RunDrain after_fr boundary))).
    {
      eapply path_extend; [exact Hr|unfold Sem.step,R.next_config; cbn [configuration R.cfg_state R.cfg_control]; now rewrite Eset].
    }
    assert (Hnext_eq : next_fr = after_fr).
    {
      exact (@live_frame_unique tf _ next_fr after_fr
        (inv_shape (proj2 (@reachable_invariants tf roots _ Hafter))) Hnext ltac:(cbn; now left)
        ltac:(rewrite (@set_value_owner _ _ _ _ _ Eset); congruence)).
    }
    subst next_fr; rewrite <- Howner in Hbelow; cbn [R.cfg_state] in Hwakes,Ho.
    destruct (@quiet_commit_queue tf roots st fr direct boundary after after_fr Hr Hbelow Hwakes Eset Ho) as [Hq Hw].
    unfold quiet_round; cbn; rewrite <- (@set_value_owner _ _ _ _ _ Eset) in Howner.
    rewrite <- Howner; split; [exact Hq|split; [exact Hw|now split]].
  - destruct Hquiet as [Howner ->]; rewrite <- Howner in Hbelow.
    pose proof (@quiet_drain_returns tf roots st fr boundary next Hr E Hbelow) as Hreturn.
    destruct (@closing_above_survivor tf roots _ next fr boundary owner Hr eq_refl Hreturn Hactive) as [_ Hneq].
    congruence.
Qed.

Theorem equal_budget_quiet_path tf roots (finite : Sem.finite_system tf roots)
  owner boundary first last first_fr last_fr :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  In first_fr (live_frames (R.cfg_control first)) -> R.frame_owner first_fr = owner ->
  In last_fr (live_frames (R.cfg_control last)) -> R.frame_owner last_fr = owner ->
  round_budget (Sem.support finite) (protected_targets (Sem.support finite) (R.cfg_state first) owner)
      (R.cfg_state last) last_fr =
    round_budget (Sem.support finite) (protected_targets (Sem.support finite) (R.cfg_state first) owner)
      (R.cfg_state first) first_fr ->
  quiet_round owner boundary first -> quiet_round owner boundary last.
Proof.
  intros Hr H; revert Hr first_fr last_fr; induction H as [c|first next last Estep Hactive Htail IH];
    intros Hr first_fr last_fr Hfirst Hofirst Hlast Holast E Hquiet; [exact Hquiet|].
  assert (Howner : In owner (Sem.support finite)).
  {
    eapply active_supported; [exact Hr|rewrite <- Hofirst; now apply live_frames_active].
  }
  destruct (@active_frame_survives tf first next first_fr Estep Hfirst ltac:(now rewrite Hofirst))
    as [next_fr [Hnext Honext]]; rewrite Hofirst in Honext.
  assert (Hprefix : active_trace tf owner first next).
  {
    eapply ActiveStep; [exact Estep|exact Hactive|constructor].
  }
  pose proof (@equal_round_budget_split tf roots finite owner
    (protected_targets (Sem.support finite) (R.cfg_state first) owner) first next last first_fr next_fr last_fr
    Hr Hprefix Htail Hfirst Hofirst Hnext Honext Hlast Holast
    (protected_targets_scoped _ _ _) (protected_owner _ _ _ Howner) E) as Ep.
  pose proof (f_equal (@fst nat (nat * nat)) Ep) as Eevaluation.
  change (evaluation_credit (Sem.support finite) (R.frame_owner next_fr) (R.cfg_state next) =
    evaluation_credit (Sem.support finite) (R.frame_owner first_fr) (R.cfg_state first)) in Eevaluation.
  rewrite Hofirst,Honext in Eevaluation.
  destruct (@equal_evaluation_credit tf roots (Sem.support finite) owner first next Hr Hprefix Eevaluation)
    as [Ha [Hs Hcontrolled]].
  pose proof (f_equal (fun vector : credit_vector => snd (snd vector)) Ep) as Ho.
  change (ordinary_credit (R.cfg_state next) next_fr = ordinary_credit (R.cfg_state first) first_fr) in Ho.
  assert (Hquiet_next : quiet_round owner boundary next).
  {
    eapply quiet_round_step; [exact Hr|exact Estep|exact Hactive|exact Hfirst|exact Hofirst|
      exact Hnext|exact Honext|exact Ha|exact Hs|exact Ho| |exact Hquiet].
    exact (@equal_round_budget_lower_potentials tf roots finite owner first next first_fr next_fr
      Hr Hprefix Hofirst Honext Howner Ep).
  }
  apply (IH (@path_extend tf _ _ _ Hr Estep) next_fr last_fr Hnext Honext Hlast Holast); [|exact Hquiet_next].
  rewrite (@equal_activation_protected_targets (Sem.support finite) tf first next owner
    ltac:(eapply Sem.StepsStep; [exact Estep|constructor]) Ha Howner).
  etransitivity; [exact E|symmetry; exact Ep].
Qed.


Lemma drain_next tf st fr k : exists after, Sem.step tf (configuration st (R.RunDrain fr k)) after.
Proof.
  unfold Sem.step,R.next_config; cbn [configuration R.cfg_state R.cfg_control].
  destruct (R.queue st) as [|head rest]; cbn [R.queue_peek R.queue_pop]; decompose_operation;
    eexists; reflexivity.
Qed.

Lemma quiet_drain_completes tf roots st fr k :
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunDrain fr k)) ->
  queue_below st (R.frame_owner fr) ->
  episode_completes tf (configuration st (R.RunDrain fr k)) (R.frame_owner fr) k.
Proof.
  intros Hr Hbelow; destruct (@drain_next tf st fr k) as [after E].
  pose proof (@quiet_drain_returns tf roots st fr k after Hr E Hbelow) as Hreturn.
  exists (R.cfg_state after); split.
  - destruct after as [final ctrl]; cbn [R.cfg_control] in Hreturn; subst ctrl.
    eapply Sem.StepsStep; [exact E|constructor].
  - exact (@close_returns_below tf roots _ after (R.frame_owner fr) k Hr E
      ltac:(exists fr; repeat split; assumption || reflexivity)).
Qed.

Definition frame_budget support st fr :=
  round_budget support (protected_targets support st (R.frame_owner fr)) st fr.
Theorem frame_budget_path tf roots (finite : Sem.finite_system tf roots) owner first last first_fr last_fr :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  In first_fr (live_frames (R.cfg_control first)) -> R.frame_owner first_fr = owner ->
  In last_fr (live_frames (R.cfg_control last)) -> R.frame_owner last_fr = owner ->
  frame_budget (Sem.support finite) (R.cfg_state last) last_fr =
    frame_budget (Sem.support finite) (R.cfg_state first) first_fr \/
  credit_lt (frame_budget (Sem.support finite) (R.cfg_state last) last_fr)
    (frame_budget (Sem.support finite) (R.cfg_state first) first_fr).
Proof.
  intros Hr H Hfirst Hofirst Hlast Holast.
  assert (Hin : In owner (Sem.support finite)).
  {
    eapply active_supported; [exact Hr|rewrite <- Hofirst; now apply live_frames_active].
  }
  pose proof (@evaluation_credit_path tf roots (Sem.support finite) owner first last Hr H) as Hle.
  destruct (Nat.eq_dec (evaluation_credit (Sem.support finite) owner (R.cfg_state last))
    (evaluation_credit (Sem.support finite) owner (R.cfg_state first))) as [Heq|Hneq].
  - pose proof (proj1 (@equal_evaluation_credit tf roots (Sem.support finite) owner first last Hr H Heq)) as Ha.
    unfold frame_budget; rewrite Hofirst,Holast.
    rewrite (@equal_activation_protected_targets (Sem.support finite) tf first last owner
      (@active_trace_path tf owner first last H) Ha Hin).
    exact (@round_budget_path tf roots finite owner
      (protected_targets (Sem.support finite) (R.cfg_state first) owner) first last first_fr last_fr
      Hr H Hfirst Hofirst Hlast Holast (protected_targets_scoped _ _ _) (protected_owner _ _ _ Hin)).
  - right; unfold credit_lt,frame_budget,round_budget; cbn; rewrite Hofirst,Holast; left; lia.
Qed.

Lemma frame_budget_equal_fixed tf roots (finite : Sem.finite_system tf roots) owner first last first_fr last_fr :
  Sem.steps tf (R.initial_config roots) first -> active_trace tf owner first last ->
  In owner (Sem.support finite) -> R.frame_owner first_fr = owner -> R.frame_owner last_fr = owner ->
  frame_budget (Sem.support finite) (R.cfg_state last) last_fr =
    frame_budget (Sem.support finite) (R.cfg_state first) first_fr ->
  round_budget (Sem.support finite) (protected_targets (Sem.support finite) (R.cfg_state first) owner)
      (R.cfg_state last) last_fr =
    round_budget (Sem.support finite) (protected_targets (Sem.support finite) (R.cfg_state first) owner)
      (R.cfg_state first) first_fr.
Proof.
  intros Hr H Hin Hofirst Holast E.
  pose proof (f_equal (@fst nat (nat * nat)) E) as Heq.
  change (evaluation_credit (Sem.support finite) (R.frame_owner last_fr) (R.cfg_state last) =
    evaluation_credit (Sem.support finite) (R.frame_owner first_fr) (R.cfg_state first)) in Heq.
  rewrite Hofirst,Holast in Heq.
  pose proof (proj1 (@equal_evaluation_credit tf roots (Sem.support finite) owner first last Hr H Heq)) as Ha.
  unfold frame_budget in E; rewrite Hofirst,Holast,
    (@equal_activation_protected_targets (Sem.support finite) tf first last owner
    (@active_trace_path tf owner first last H) Ha Hin) in E; exact E.
Qed.

Lemma episode_complete_prefix tf first middle owner k :
  Sem.steps tf first middle -> episode_completes tf middle owner k ->
  episode_completes tf first owner k.
Proof.
  intros H [final [Htail Hbelow]]; exists final; split; [eapply path_join; eassumption|exact Hbelow].
Qed.

Theorem quiet_round_descent tf roots (finite : Sem.finite_system tf roots) st fr body k :
  higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr body k)) ->
  queue_below st (R.frame_owner fr) -> R.deferred_wakes st = [] ->
  episode_completes tf (configuration st (R.RunRhs fr body k)) (R.frame_owner fr) k \/
  exists next next_fr,
    Sem.steps tf (configuration st (R.RunRhs fr body k))
      (configuration next (R.RunRhs next_fr (tf (R.frame_owner fr)) k)) /\
    R.frame_owner next_fr = R.frame_owner fr /\ queue_below next (R.frame_owner fr) /\
    R.deferred_wakes next = [] /\
    credit_lt (frame_budget (Sem.support finite) next next_fr) (frame_budget (Sem.support finite) st fr).
Proof.
  intros Hhigher Hr Hbelow Hwakes.
  destruct (@rhs_evaluation_finishes tf roots body st fr k Hhigher Hr)
    as [committed [commit_fr [direct [Heval Hcommit_owner]]]].
  assert (Hcommit : Sem.steps tf (R.initial_config roots) (configuration committed (R.RunCommit commit_fr direct k)))
    by (eapply path_join; eassumption).
  destruct (R.set_value (R.flush_deferred committed) commit_fr direct) as [drained drain_fr] eqn:Eset.
  assert (Estep : Sem.step tf (configuration committed (R.RunCommit commit_fr direct k))
    (configuration drained (R.RunDrain drain_fr k))).
  {
    unfold Sem.step,R.next_config; cbn [configuration R.cfg_state R.cfg_control]; now rewrite Eset.
  }
  assert (Hprefix : Sem.steps tf (configuration st (R.RunRhs fr body k)) (configuration drained (R.RunDrain drain_fr k))).
  {
    eapply path_join; [exact Heval|eapply Sem.StepsStep; [exact Estep|constructor]].
  }
  assert (Hreach : Sem.steps tf (R.initial_config roots) (configuration drained (R.RunDrain drain_fr k)))
    by (eapply path_join; [exact Hr|exact Hprefix]).
  assert (Howner : R.frame_owner drain_fr = R.frame_owner fr).
  {
    rewrite (@set_value_owner _ _ _ _ _ Eset); exact Hcommit_owner.
  }
  destruct (@path_before_episode_return tf roots (R.frame_owner fr) k _ _ Hr
    ltac:(cbn; left; now split) Hprefix) as [Hdone|[Hactive Hlive]]; [now left|].
  destruct (@drain_evaluation_finishes tf roots (S (length (Sem.support finite))) drained drain_fr k
    ltac:(now rewrite Howner) Hreach (@reachable_queue_ceiling tf roots finite _ Hreach))
    as [[next ctrl] [Hsuffix [Hnext_below [Hnext_wakes Hboundary]]]].
  cbn [R.cfg_state R.cfg_control] in Hnext_below,Hnext_wakes,Hboundary.
  rewrite Howner in Hnext_below,Hboundary.
  destruct Hboundary as [->|[next_fr [-> Hnext_owner]]].
  - left; exists next; split; [eapply path_join; eassumption|exact Hnext_below].
  - destruct (@path_before_episode_return tf roots (R.frame_owner fr) k _ _ Hreach Hlive Hsuffix)
      as [Hdone|[Htail Htail_live]].
    + left; exact (@episode_complete_prefix tf _ _ (R.frame_owner fr) k Hprefix Hdone).
    + assert (Hwhole : active_trace tf (R.frame_owner fr)
        (configuration st (R.RunRhs fr body k)) (configuration next (R.RunRhs next_fr (tf (R.frame_owner fr)) k))).
      {
        eapply active_trace_join; eassumption.
      }
      destruct (@frame_budget_path tf roots finite (R.frame_owner fr) _ _ fr next_fr Hr Hwhole
        ltac:(cbn; now left) eq_refl ltac:(cbn; now left) Hnext_owner) as [Hequal|Hstrict].
      * pose proof (@active_supported tf roots finite _ (R.frame_owner fr) Hr ltac:(cbn; now left)) as Hin.
        pose proof (@frame_budget_equal_fixed tf roots finite (R.frame_owner fr) _ _ fr next_fr
          Hr Hwhole Hin eq_refl Hnext_owner Hequal) as Efixed.
        pose proof (@equal_round_budget_split tf roots finite (R.frame_owner fr)
          (protected_targets (Sem.support finite) st (R.frame_owner fr)) _ _ _ fr drain_fr next_fr
          Hr Hactive Htail ltac:(cbn; now left) eq_refl ltac:(cbn; now left) Howner
          ltac:(cbn; now left) Hnext_owner (protected_targets_scoped _ _ _) (protected_owner _ _ _ Hin) Efixed) as Eprefix.
        pose proof (@equal_budget_quiet_path tf roots finite (R.frame_owner fr) k _ _ fr drain_fr
          Hr Hactive ltac:(cbn; now left) eq_refl ltac:(cbn; now left) Howner Eprefix
          ltac:(unfold quiet_round; cbn; repeat split; assumption || reflexivity)) as Hquiet.
        destruct Hquiet as [Hquiet_below _]; cbn [R.cfg_state] in Hquiet_below.
        left; eapply episode_complete_prefix; [exact Hprefix|].
        rewrite <- Howner; exact (@quiet_drain_completes tf roots drained drain_fr k Hreach
          ltac:(now rewrite Howner)).
      * right; exists next,next_fr; repeat split; try assumption.
        exact (@active_trace_path tf (R.frame_owner fr) _ _ Hwhole).
Qed.

Theorem quiet_rhs_completes tf roots (finite : Sem.finite_system tf roots) st fr body k :
  higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr body k)) ->
  queue_below st (R.frame_owner fr) -> R.deferred_wakes st = [] ->
  episode_completes tf (configuration st (R.RunRhs fr body k)) (R.frame_owner fr) k.
Proof.
  assert (Hfinish : forall budget st fr body k,
    frame_budget (Sem.support finite) st fr = budget ->
    higher_completion tf roots (R.frame_owner fr) ->
    Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr body k)) ->
    queue_below st (R.frame_owner fr) -> R.deferred_wakes st = [] ->
    episode_completes tf (configuration st (R.RunRhs fr body k)) (R.frame_owner fr) k).
  {
    intro budget; induction budget as [budget IH] using (well_founded_induction credit_lt_well_founded).
    intros first first_fr first_body boundary Ebudget Hhigher Hr Hbelow Hwakes.
    destruct (@quiet_round_descent tf roots finite first first_fr first_body boundary Hhigher Hr Hbelow Hwakes)
      as [Hdone|[next [next_fr [Hpath [Howner [Hq [Hw Hstrict]]]]]]]; [exact Hdone|].
    eapply episode_complete_prefix; [exact Hpath|].
    rewrite <- Howner.
    apply (IH (frame_budget (Sem.support finite) next next_fr) ltac:(now rewrite <- Ebudget)).
    - reflexivity.
    - now rewrite Howner.
    - rewrite Howner; eapply path_join; [exact Hr|exact Hpath].
    - now rewrite Howner.
    - exact Hw.
  }
  exact (Hfinish (frame_budget (Sem.support finite) st fr) st fr body k eq_refl).
Qed.

Theorem rhs_episode_completes tf roots (finite : Sem.finite_system tf roots) st fr body k :
  higher_completion tf roots (R.frame_owner fr) ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.RunRhs fr body k)) ->
  episode_completes tf (configuration st (R.RunRhs fr body k)) (R.frame_owner fr) k.
Proof.
  intros Hhigher Hr.
  destruct (@rhs_round_boundary tf roots finite st fr body k Hhigher Hr)
    as [[next ctrl] [Hpath [Hq [Hw Hboundary]]]].
  cbn [R.cfg_state R.cfg_control] in Hq,Hw,Hboundary.
  destruct Hboundary as [->|[next_fr [-> Howner]]].
  - exists next; split; assumption.
  - eapply episode_complete_prefix; [exact Hpath|].
    rewrite <- Howner; eapply quiet_rhs_completes.
    + exact finite.
    + now rewrite Howner.
    + rewrite Howner; eapply path_join; [exact Hr|exact Hpath].
    + now rewrite Howner.
    + exact Hw.
Qed.

Theorem start_episode_completes tf roots (finite : Sem.finite_system tf roots) st owner k :
  higher_completion tf roots owner ->
  Sem.steps tf (R.initial_config roots) (configuration st (R.StartEpisode owner k)) ->
  episode_completes tf (configuration st (R.StartEpisode owner k)) owner k.
Proof.
  intros Hhigher Hr.
  set (prepared := R.clear_side_dirty (R.materialize st owner) owner).
  set (fr := R.fresh_frame prepared owner (U.initial_phase false owner)).
  assert (E : Sem.step tf (configuration st (R.StartEpisode owner k))
    (configuration prepared (R.RunRhs fr (tf owner) k))) by reflexivity.
  eapply episode_complete_prefix; [eapply Sem.StepsStep; [exact E|constructor]|].
  change (episode_completes tf (configuration prepared (R.RunRhs fr (tf owner) k)) (R.frame_owner fr) k).
  apply (@rhs_episode_completes tf roots finite).
  - exact Hhigher.
  - eapply path_extend; eassumption.
Qed.

Theorem reachable_episode_completes tf roots (finite : Sem.finite_system tf roots) st owner k :
  Sem.steps tf (R.initial_config roots) (configuration st (R.StartEpisode owner k)) ->
  episode_completes tf (configuration st (R.StartEpisode owner k)) owner k.
Proof.
  assert (Hfinish : forall distance st owner k,
    length (Sem.support finite) - priority st owner = distance ->
    Sem.steps tf (R.initial_config roots) (configuration st (R.StartEpisode owner k)) ->
    episode_completes tf (configuration st (R.StartEpisode owner k)) owner k).
  {
    intro distance; induction distance using lt_wf_ind; intros first current boundary Edistance Hr.
    apply (@start_episode_completes tf roots finite first current boundary); [|exact Hr].
    intros next child child_k Hchild Hhigher.
    destruct (@rank_lt_ranked next current child Hhigher) as [Hcurrent Hchild_rank].
    assert (Hinitial_rank : ranked first current).
    {
      exact (Forall_inv (shape_stack_ranks (inv_shape (proj2 (@reachable_invariants tf roots _ Hr))))).
    }
    pose proof (@reachable_priority_agrees tf roots
      (configuration first (R.StartEpisode current boundary))
      (configuration next (R.StartEpisode child child_k)) current Hr Hchild Hinitial_rank Hcurrent) as Hsame.
    change (priority first current = priority next current) in Hsame.
    pose proof (proj1 (@compare_rank next current child Hcurrent Hchild_rank) Hhigher) as Hlt.
    destruct Hchild_rank as [rank Hrank].
    pose proof (@reachable_rank_bound tf roots finite _ child rank Hchild Hrank) as Hbound.
    change (Ranks.lookup (R.ranking next) child = Some rank) in Hrank.
    assert (Hchild_priority : priority next child = S rank) by (unfold priority; now rewrite Hrank).
    apply (H (length (Sem.support finite) - priority next child)).
    - lia.
    - reflexivity.
    - exact Hchild.
  }
  exact (Hfinish (length (Sem.support finite) - priority st owner) st owner k eq_refl).
Qed.

Theorem finite_system_terminates tf roots : Sem.finite_system tf roots ->
  exists final, Sem.terminates_to tf roots final.
Proof.
  intro finite; apply (@finish_from_episodes tf roots finite).
  exact (@reachable_episode_completes tf roots finite).
Qed.

Theorem finite_system_has_fuel tf roots : Sem.finite_system tf roots ->
  exists fuel final, R.solve_fuel fuel tf roots = Some final.
Proof.
  intro finite; apply (@fuel_from_episodes tf roots finite).
  exact (@reachable_episode_completes tf roots finite).
Qed.


End EpisodeCredits.

End Make.

(** OneBox precision for the bundled public interface. The public theorem
    file packages these proofs in the common fixedness and fallback records. *)
Module OrdinaryFixedPoint (P : ORDINARY_FIXED_POINT_PARAMETERS).
  Module U := P.FixedU.
  Module Sound := OrdinaryUpdateSoundAdapter P.V P.D U P.FixedUL.
  Module Core := Make P.V P.D U P.FixedSU P.S P.M P.Features
    P.DL Sound P.FixedSUL P.SL P.ML.
  Module R := Core.R.
  Module Quiet := Core.QuietFixedness P.FixedUL.
  Definition control_avoids_fallback ctrl :=
    Forall (fun fr => U.avoids_fallback (R.frame_phase fr)) (Core.live_frames ctrl).
  Definition phase_narrow phase := phase = U.BoxN.
  Lemma initial_wide owner : ~ phase_narrow (U.initial_phase false owner).
  Proof. discriminate. Qed.
  Lemma update_safe owner phase old input : U.avoids_fallback phase ->
    (phase_narrow phase -> P.D.leq input old = true) ->
    U.avoids_fallback (fst (U.update false owner phase old input)).
  Proof. exact (@U.admissible_update_avoids_fallback false owner phase old input). Qed.
  Lemma update_narrow owner phase old input : U.avoids_fallback phase ->
    phase_narrow (fst (U.update false owner phase old input)) -> P.D.leq input old = true.
  Proof.
    intros Hsafe Hnarrow; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
      unfold U.update,phase_narrow in Hnarrow; destruct (P.D.leq input old) eqn:Hbelow;
      cbn in Hnarrow; try discriminate; reflexivity.
  Qed.
  Lemma update_descends owner phase old input : U.avoids_fallback phase ->
    P.D.leq input old = true -> P.D.leq (snd (U.update false owner phase old input)) old = true.
  Proof.
    intros Hsafe Hbelow; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
      unfold U.update; rewrite Hbelow; apply P.WNL.narrow_upper; exact Hbelow.
  Qed.
  Lemma safe_narrows owner phase old input : U.avoids_fallback phase ->
    P.D.leq input old = true -> Core.eqv (snd (U.update false owner phase old input)) (P.WN.narrow old input).
  Proof.
    intros Hsafe Hbelow; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
      unfold U.update; rewrite Hbelow; split; apply P.DL.leq_refl.
  Qed.
  Theorem ordinary_avoids_fallback tf roots : P.Features.defer_spawns = true ->
    Core.monotonic_system tf -> Core.no_side_effects tf ->
    forall c, Core.Sem.steps tf (R.initial_config roots) c -> control_avoids_fallback (R.cfg_control c).
  Proof.
    intros Hdefer Hmono Hpure c Hr.
    exact (@Core.ordinary_wave_safe U.avoids_fallback phase_narrow
      (fun owner => @U.initial_avoids_fallback false owner) initial_wide
      update_safe update_narrow update_descends tf roots c Hdefer Hpure Hmono Hr).
  Qed.
  Definition successful_run_narrowing_fixed := @Quiet.successful_run_fixed
    P.WN.narrow U.avoids_fallback P.WNL.narrow_lower P.WNL.narrow_upper safe_narrows phase_narrow
    (fun owner => @U.initial_avoids_fallback false owner) initial_wide
    update_safe update_narrow update_descends.
End OrdinaryFixedPoint.
