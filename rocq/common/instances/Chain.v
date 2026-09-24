From Stdlib Require Import List Arith.PeanoNat Lia Sorting.Permutation.
From TcSolvers Require Import
  common.Assumptions
  common.BoxUpdate
  common.Collections
  solvers.slr.common.DiscoveryOrder
  common.FiniteHeight.

Import ListNotations.

(** Shared concrete instance: a five-element chain with slow, non-idempotent
    narrowing, constructive update credits, and list-based collections. *)
Module Chain.
  Module V.
    Definition t := nat.
    Definition eq_dec := Nat.eq_dec.
  End V.

  Module D.
    Inductive value := Bot | One | Two | Three | Top.
    Definition t := value.
    Definition bottom := Bot.

    Definition rank (x : t) : nat :=
      match x with
      | Bot => 0 | One => 1 | Two => 2 | Three => 3 | Top => 4
      end.

    Definition leq (left right : t) : bool :=
      Nat.leb (rank left) (rank right).

    Definition join (left right : t) : t :=
      if leq left right then right else left.
  End D.

  Module WN.
    Definition widen (old input : D.t) : D.t :=
      if D.leq input old then old else D.Top.

    Definition narrow (old input : D.t) : D.t :=
      if D.leq old input then input else
      match old with
      | D.Bot => D.Bot
      | D.One => D.One
      | D.Two => D.One
      | D.Three => D.Two
      | D.Top => D.Three
      end.
  End WN.

  Module U := OneBoxUpdate V D WN.

  Module DL <: DOMAIN_LAWS D.
    Lemma leq_refl : forall x, D.leq x x = true.
    Proof. destruct x; reflexivity. Qed.

    Lemma leq_trans : forall x y z,
      D.leq x y = true -> D.leq y z = true -> D.leq x z = true.
    Proof. destruct x, y, z; cbn; congruence. Qed.

    Lemma bottom_least : forall x, D.leq D.bottom x = true.
    Proof. destruct x; reflexivity. Qed.

    Lemma join_upper_left : forall x y,
      D.leq x (D.join x y) = true.
    Proof. destruct x, y; reflexivity. Qed.

    Lemma join_upper_right : forall x y,
      D.leq y (D.join x y) = true.
    Proof. destruct x, y; reflexivity. Qed.

    Lemma join_least : forall x y z,
      D.leq x z = true -> D.leq y z = true ->
      D.leq (D.join x y) z = true.
    Proof. destruct x, y, z; cbn; congruence. Qed.

    Lemma join_commutative : forall x y,
      D.leq (D.join x y) (D.join y x) = true /\
      D.leq (D.join y x) (D.join x y) = true.
    Proof. destruct x, y; split; reflexivity. Qed.

    Lemma join_associative : forall x y z,
      D.leq (D.join (D.join x y) z) (D.join x (D.join y z)) = true /\
      D.leq (D.join x (D.join y z)) (D.join (D.join x y) z) = true.
    Proof. destruct x, y, z; split; reflexivity. Qed.
  End DL.

  Module WNL <: WIDEN_NARROW_LAWS D WN.
    Lemma widen_upper_old : forall old input,
      D.leq old (WN.widen old input) = true.
    Proof. destruct old, input; reflexivity. Qed.

    Lemma widen_upper_input : forall old input,
      D.leq input (WN.widen old input) = true.
    Proof. destruct old, input; reflexivity. Qed.

    Lemma narrow_lower : forall old input,
      D.leq input old = true ->
      D.leq input (WN.narrow old input) = true.
    Proof. destruct old, input; cbn; congruence. Qed.

    Lemma narrow_upper : forall old input,
      D.leq input old = true ->
      D.leq (WN.narrow old input) old = true.
    Proof. destruct old, input; cbn; congruence. Qed.
  End WNL.

  Module WS <: WIDEN_STABILITY D WN.
    Lemma widen_stable : forall old input,
      D.leq input old = true ->
      D.leq (WN.widen old input) old = true /\
      D.leq old (WN.widen old input) = true.
    Proof.
      intros old input Hle. unfold WN.widen. rewrite Hle.
      split; apply DL.leq_refl.
    Qed.
  End WS.

  (** Keep the laws reusable across separately generated OneBox phase types. *)
  Module Type BOX.
    Inductive phase_state : Type :=
    | BoxW
    | BoxN
    | Widen.
  
    Definition phase := phase_state.
  
    Definition initial_phase
      (_is_side : bool) (_variable : V.t) : phase :=
      BoxW.
  
    Definition update
      (_is_side : bool) (_variable : V.t)
      (current : phase) (old input : D.t) : phase * D.t :=
      match current with
      | BoxW =>
          if D.leq input old
          then (BoxN, WN.narrow old input)
          else (BoxW, WN.widen old input)
      | BoxN =>
          if D.leq input old
          then (BoxN, WN.narrow old input)
          else (Widen, WN.widen old input)
      | Widen =>
          (Widen, WN.widen old input)
      end.
  End BOX.

  Module UpdateLaws (U : BOX) <: UPDATE_LAWS V D U.
    Definition equivalent (x y : D.t) : Prop :=
      D.leq x y = true /\ D.leq y x = true.

    Lemma equivalent_eq : forall x y, equivalent x y -> x = y.
    Proof. destruct x, y; unfold equivalent; cbn; intuition discriminate. Qed.

    Lemma equivalent_refl : forall x, equivalent x x.
    Proof. intro x. split; apply DL.leq_refl. Qed.

    Lemma update_sound : forall is_side variable phase old input,
      D.leq input
        (snd (U.update is_side variable phase old input)) = true.
    Proof. intros. destruct phase, old, input; reflexivity. Qed.

    Lemma update_extensional : forall is_side variable phase old old' input input',
      equivalent old old' -> equivalent input input' ->
      equivalent
        (snd (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old' input')).
    Proof.
      intros is_side variable phase old old' input input' Hold Hinput.
      apply equivalent_eq in Hold, Hinput. subst. apply equivalent_refl.
    Qed.

    Lemma update_stutter_closed : forall is_side variable phase old input,
      equivalent (snd (U.update is_side variable phase old input)) old ->
      forall old' input', equivalent old' old -> equivalent input' input ->
      equivalent
        (snd (U.update is_side variable
          (fst (U.update is_side variable phase old input)) old' input'))
        old'.
    Proof.
      intros is_side variable phase old input Hstutter old' input' Hold Hinput.
      apply equivalent_eq in Hold, Hinput. subst old' input'.
      destruct phase, old, input; cbn in *;
        try exact Hstutter;
        unfold equivalent in *; cbn in *; intuition discriminate.
    Qed.

    Definition remaining_changes (phase : U.phase) (old : D.t) : nat :=
      match phase with
      | U.BoxW => 10 - D.rank old
      | U.BoxN => S (D.rank old)
      | U.Widen => if D.leq D.Top old then 0 else 1
      end.

    Lemma remaining_changes_extensional : forall phase old old',
      equivalent old old' ->
      remaining_changes phase old = remaining_changes phase old'.
    Proof. intros phase old old' H. apply equivalent_eq in H. now subst. Qed.

    Lemma remaining_changes_nonincreasing : forall is_side variable phase old input,
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <=
      remaining_changes phase old.
    Proof. intros. destruct phase, old, input; cbn; lia. Qed.

    Lemma update_change_consumes : forall is_side variable phase old input,
      ~ equivalent
          (snd (U.update is_side variable phase old input)) old ->
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <
      remaining_changes phase old.
    Proof.
      intros is_side variable phase old input Hchange.
      destruct phase, old, input; cbn in *;
        try lia; exfalso; apply Hchange; split; reflexivity.
    Qed.
  End UpdateLaws.
  Module UL := UpdateLaws U.

  Module S := ListSet V.
  Module M := AssocMap V.
  Module SL <: SET_LAWS V S.
    Lemma mem_spec : forall x xs, S.mem x xs = true <-> In x (S.elements xs).
    Proof.
      intros x xs. unfold S.mem, S.elements.
      match goal with |- context [if ?test then _ else _] =>
        destruct test end; intuition congruence.
    Qed.
    Lemma empty_spec : forall x, S.mem x S.empty = false.
    Proof. reflexivity. Qed.
    Lemma add_spec : forall x y xs,
      S.mem x (S.add y xs) = true <-> x = y \/ S.mem x xs = true.
    Proof.
      intros x y xs. rewrite !mem_spec. unfold S.add, S.elements.
      match goal with |- context [if ?test then _ else _] =>
        destruct test end; cbn in *; intuition congruence.
    Qed.
  End SL.

  Module ML <: MAP_LAWS V M.
    Lemma values_empty : forall A, M.values (M.empty A) = [].
    Proof. reflexivity. Qed.
    Lemma lookup_empty : forall A x, M.lookup (M.empty A) x = None.
    Proof. reflexivity. Qed.
    Lemma lookup_update_same : forall A (m : M.t A) x value,
      M.lookup (M.update m x value) x = Some value.
    Proof.
      intros A m x value. induction m as [|[y old] rest IH]; cbn;
        destruct (V.eq_dec x y) as [->|H] || destruct (V.eq_dec x x);
        cbn; repeat destruct V.eq_dec; subst; try congruence.
    Qed.
    Lemma lookup_update_other : forall A (m : M.t A) x y value,
      x <> y -> M.lookup (M.update m y value) x = M.lookup m x.
    Proof.
      intros A m x y value H. induction m as [|[z old] rest IH]; cbn;
        repeat destruct V.eq_dec; cbn; repeat destruct V.eq_dec;
        subst; congruence.
    Qed.
    Lemma lookup_values : forall A (m : M.t A) x value,
      M.lookup m x = Some value -> In value (M.values m).
    Proof.
      intros A m x value. induction m as [|[y old] rest IH]; cbn.
      - discriminate.
      - destruct (V.eq_dec x y); intro H.
        + inversion H. now left.
        + right. now apply IH.
    Qed.
    Lemma values_update : forall A (m : M.t A) x value,
      exists rest,
        Permutation (M.values (M.update m x value)) (value :: rest) /\
        match M.lookup m x with
        | Some previous => Permutation (M.values m) (previous :: rest)
        | None => Permutation (M.values m) rest
        end.
    Proof.
      intros A m x value. induction m as [|[y old] tail [rest [Hnew Hold]]].
      - exists []. split; apply Permutation_refl.
      - cbn. destruct (V.eq_dec x y).
        + exists (M.values tail). split; apply Permutation_refl.
        + exists (old :: rest). split.
          * eapply Permutation_trans; [apply perm_skip; exact Hnew |].
            apply perm_swap.
          * destruct (M.lookup tail x).
            -- eapply Permutation_trans; [apply perm_skip; exact Hold |].
               apply perm_swap.
            -- now apply perm_skip.
    Qed.
  End ML.
  Module Height <: FINITE_HEIGHT_LAWS D DL.
    Definition equivalent := UL.equivalent.
    Definition remaining_height (x : D.t) := 4 - D.rank x.

    Lemma remaining_height_extensional x y :
      equivalent x y -> remaining_height x = remaining_height y.
    Proof. intro H. apply UL.equivalent_eq in H. now subst. Qed.

    Lemma strict_ascent_decreases lower upper :
      D.leq lower upper = true -> ~ equivalent upper lower ->
      remaining_height upper < remaining_height lower.
    Proof.
      destruct lower, upper; unfold equivalent, UL.equivalent; cbn;
        intros Hle Hstrict; try discriminate; try lia;
        exfalso; apply Hstrict; split; reflexivity.
    Qed.
  End Height.
End Chain.
