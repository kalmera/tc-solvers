From Stdlib Require Import List.
From TcSolvers Require Import common.Assumptions.

Import ListNotations.
Set Implicit Arguments.

(** Shared valuation and observation-order vocabulary.  RHS observation
    relations remain variant-local because each solver functor exports its own
    generative transfer-tree type. *)
Module Make (V : VAR) (D : DOMAIN).
  Definition valuation := V.t -> D.t.

  Definition valuation_le_on
    (variables : list V.t) (lower upper : valuation) : Prop :=
    forall variable,
      List.In variable variables ->
      D.leq (lower variable) (upper variable) = true.

  Record observation : Type := {
    observed_direct : D.t;
    observed_reads : list (V.t * D.t);
    observed_sides : list (V.t * D.t);
    observed_spawns : list V.t;
  }.

  Definition reads_at (values : valuation) (result : observation) : Prop :=
    forall target value,
      List.In (target, value) (observed_reads result) ->
      value = values target.

  Definition list_included {A : Type}
    (lower upper : list A) : Prop :=
    forall value, List.In value lower -> List.In value upper.

  Definition valued_events_le
    (lower upper : list (V.t * D.t)) : Prop :=
    forall target lower_value,
      List.In (target, lower_value) lower ->
      exists upper_value,
        List.In (target, upper_value) upper /\
        D.leq lower_value upper_value = true.

  Definition common_read_values_le
    (lower upper : observation) : Prop :=
    forall target lower_value upper_value,
      List.In (target, lower_value) (observed_reads lower) ->
      List.In (target, upper_value) (observed_reads upper) ->
      D.leq lower_value upper_value = true.

  Record effects_le (lower upper : observation) : Prop := {
    direct_effect_le :
      D.leq (observed_direct lower) (observed_direct upper) = true;
    side_effects_le :
      valued_events_le (observed_sides lower) (observed_sides upper);
    spawn_effects_le :
      list_included (observed_spawns lower) (observed_spawns upper);
  }.

  Definition side_effects_below
    (values : valuation) (effects : list (V.t * D.t)) : Prop :=
    forall target value,
      List.In (target, value) effects ->
      D.leq value (values target) = true.

  Definition prefix_reads_below
    (upper : valuation) (reads : list (V.t * D.t)) : Prop :=
    forall target value,
      List.In (target, value) reads ->
      D.leq value (upper target) = true.

  Lemma prefix_reads_below_snoc :
    forall upper reads target value,
      prefix_reads_below upper reads ->
      D.leq value (upper target) = true ->
      prefix_reads_below upper (reads ++ [(target, value)]).
  Proof.
    intros upper reads target value Hreads Hvalue
      observed observed_value Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - now apply Hreads with (target := observed).
    - cbn in Hin. destruct Hin as [Hequal | Hin]; [|contradiction].
      inversion Hequal. subst. exact Hvalue.
  Qed.

  Lemma reads_at_common_values :
    forall lower_values upper_values lower upper,
      reads_at lower_values lower ->
      reads_at upper_values upper ->
      (forall target,
        List.In target (List.map fst (observed_reads lower)) ->
        List.In target (List.map fst (observed_reads upper)) ->
        D.leq (lower_values target) (upper_values target) = true) ->
      common_read_values_le lower upper.
  Proof.
    intros lower_values upper_values lower upper
      Hlower_reads Hupper_reads Hvalues
      target lower_value upper_value Hinlower Hinupper.
    rewrite (Hlower_reads target lower_value Hinlower),
      (Hupper_reads target upper_value Hinupper).
    apply Hvalues.
    - apply in_map_iff. exists (target, lower_value). now split.
    - apply in_map_iff. exists (target, upper_value). now split.
  Qed.
End Make.
