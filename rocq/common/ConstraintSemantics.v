From Stdlib Require Import List.
From TcSolvers Require Import
  common.ConstraintSystems
  common.Observations.

Import ListNotations.
Set Implicit Arguments.

(** Solver-independent semantics of transfer trees and finite constraint
    systems.  This module is proof-only and is not part of extraction. *)
Module Make
  (V : VAR)
  (D : DOMAIN)
  (CS : ConstraintSystems.S V D).

  Module Observation := Observations.Make V D.

  Definition valuation := Observation.valuation.
  Definition valuation_le_on := Observation.valuation_le_on.
  Definition observation := Observation.observation.
  Definition observed_direct := Observation.observed_direct.
  Definition observed_reads := Observation.observed_reads.
  Definition observed_sides := Observation.observed_sides.
  Definition observed_spawns := Observation.observed_spawns.
  Definition reads_at := Observation.reads_at.
  Definition list_included := @Observation.list_included.
  Definition valued_events_le := Observation.valued_events_le.
  Definition common_read_values_le := Observation.common_read_values_le.
  Definition effects_le := Observation.effects_le.
  Definition valuation_side_effects_below := Observation.side_effects_below.

  (** A structural observation records every read, side effect, and spawn of
      one path through a transfer tree. *)
  Inductive rhs_observes : CS.rhs -> observation -> Prop :=
  | ObserveRet :
      forall direct,
        rhs_observes (CS.Ret direct)
          {| Observation.observed_direct := direct;
             Observation.observed_reads := [];
             Observation.observed_sides := [];
             Observation.observed_spawns := [] |}
  | ObserveGet :
      forall target value next result,
        rhs_observes (next value) result ->
        rhs_observes (CS.Get target next)
          {| Observation.observed_direct := observed_direct result;
             Observation.observed_reads :=
               (target, value) :: observed_reads result;
             Observation.observed_sides := observed_sides result;
             Observation.observed_spawns := observed_spawns result |}
  | ObserveSide :
      forall target payload next result,
        rhs_observes next result ->
        rhs_observes (CS.Side target payload next)
          {| Observation.observed_direct := observed_direct result;
             Observation.observed_reads := observed_reads result;
             Observation.observed_sides :=
               (target, payload) :: observed_sides result;
             Observation.observed_spawns := observed_spawns result |}
  | ObserveSpawn :
      forall target next result,
        rhs_observes next result ->
        rhs_observes (CS.Spawn target next)
          {| Observation.observed_direct := observed_direct result;
             Observation.observed_reads := observed_reads result;
             Observation.observed_sides := observed_sides result;
             Observation.observed_spawns :=
               target :: observed_spawns result |}.

  Definition observes_at
    (values : valuation) (body : CS.rhs) (result : observation) : Prop :=
    rhs_observes body result /\ reads_at values result.

  (** Replay a transfer against a partial store.  [None] prevents a read from
      silently treating an unmaterialized variable as bottom. *)
  Inductive rhs_eval_with (lookup : V.t -> option D.t) :
    CS.rhs -> D.t -> list (V.t * D.t) -> list (V.t * D.t) -> Prop :=
  | EvalRet :
      forall direct,
        rhs_eval_with lookup (CS.Ret direct) direct [] []
  | EvalGet :
      forall target value next direct reads effects,
        lookup target = Some value ->
        rhs_eval_with lookup (next value) direct reads effects ->
        rhs_eval_with lookup (CS.Get target next)
          direct ((target, value) :: reads) effects
  | EvalSide :
      forall target value next direct reads effects,
        rhs_eval_with lookup next direct reads effects ->
        rhs_eval_with lookup (CS.Side target value next)
          direct reads ((target, value) :: effects)
  | EvalSpawn :
      forall target next direct reads effects,
        rhs_eval_with lookup next direct reads effects ->
        rhs_eval_with lookup (CS.Spawn target next) direct reads effects.

  Lemma rhs_eval_reads_lookup : forall lookup body direct reads effects,
    rhs_eval_with lookup body direct reads effects ->
    forall target value, List.In (target, value) reads -> lookup target = Some value.
  Proof.
    intros lookup body direct reads effects Heval. induction Heval;
      intros observed value' Hin; cbn in Hin.
    - contradiction.
    - destruct Hin as [Heq | Hin];
        [inversion Heq; subst; exact H |now apply IHHeval].
    - now apply IHHeval.
    - now apply IHHeval.
  Qed.

  Inductive rhs_supported
    (supported : V.t -> Prop) : CS.rhs -> Prop :=
  | SupportedRet :
      forall value,
        rhs_supported supported (CS.Ret value)
  | SupportedGet :
      forall target next,
        supported target ->
        (forall value, rhs_supported supported (next value)) ->
        rhs_supported supported (CS.Get target next)
  | SupportedSide :
      forall target value next,
        supported target ->
        rhs_supported supported next ->
        rhs_supported supported (CS.Side target value next)
  | SupportedSpawn :
      forall target next,
        supported target ->
        rhs_supported supported next ->
        rhs_supported supported (CS.Spawn target next).

  Definition rhs_dependencies_monotone (body : CS.rhs) : Prop :=
    forall lower upper,
      rhs_observes body lower ->
      rhs_observes body upper ->
      common_read_values_le lower upper ->
      list_included
        (List.map fst (observed_reads lower))
        (List.map fst (observed_reads upper)).

  Definition rhs_effects_monotone (body : CS.rhs) : Prop :=
    forall lower upper,
      rhs_observes body lower ->
      rhs_observes body upper ->
      valued_events_le
        (observed_reads lower) (observed_reads upper) ->
      effects_le lower upper.

  Record system_monotone_on
    (tf : CS.system) (variables : list V.t) : Prop := {
    system_dependencies_monotone :
      forall owner,
        List.In owner variables ->
        rhs_dependencies_monotone (tf owner);
    system_effects_monotone :
      forall owner,
        List.In owner variables ->
        rhs_effects_monotone (tf owner);
  }.

  Definition post_solution_on
    (tf : CS.system) (variables : list V.t) (values : valuation) : Prop :=
    forall owner,
      List.In owner variables ->
      forall result,
        observes_at values (tf owner) result ->
        D.leq (observed_direct result) (values owner) = true /\
        valuation_side_effects_below values (observed_sides result) /\
        list_included (observed_spawns result) variables.

  (** The covered unknowns include every spawn encountered at this valuation. *)
  Definition spawn_closed_on
    (tf : CS.system) (variables : list V.t) (values : valuation) : Prop :=
    forall owner, List.In owner variables ->
      forall result, observes_at values (tf owner) result ->
        list_included (observed_spawns result) variables.

  Lemma post_solution_on_intro : forall tf variables values,
    spawn_closed_on tf variables values ->
    (forall owner, List.In owner variables ->
      forall result, observes_at values (tf owner) result ->
        D.leq (observed_direct result) (values owner) = true /\
        valuation_side_effects_below values (observed_sides result)) ->
    post_solution_on tf variables values.
  Proof.
    intros tf variables values Hclosed Hvalues owner Hin result Hobs.
    destruct (Hvalues owner Hin result Hobs) as [Hdirect Hsides].
    split; [exact Hdirect |]. split; [exact Hsides |].
    exact (Hclosed owner Hin result Hobs).
  Qed.

  Definition least_solution_on
    (tf : CS.system) (variables : list V.t) (values : valuation) : Prop :=
    post_solution_on tf variables values /\
    forall upper,
      post_solution_on tf variables upper ->
      valuation_le_on variables values upper.

  Record finite_system (tf : CS.system) (initial : list V.t) : Type := {
    support : list V.t;
    support_nodup : NoDup support;
    initial_supported :
      forall x, List.In x initial -> List.In x support;
    system_supported :
      forall x,
        List.In x support ->
        rhs_supported (fun y => List.In y support) (tf x);
  }.

  Record closed_finite_system
    (tf : CS.system) (variables : list V.t) : Prop := {
    closed_variables_nodup : NoDup variables;
    closed_system_supported :
      forall owner,
        List.In owner variables ->
        rhs_supported
          (fun target => List.In target variables) (tf owner);
  }.

End Make.
