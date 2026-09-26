From Stdlib Require Import List.
From TcSolvers Require Import common.ConstraintSemantics common.Interfaces.

Set Implicit Arguments.

(** The part of a solver state used by its public specifications. *)
Module Type STORE (V : VAR) (D : DOMAIN) (M : MAP V).
  Parameter state : Type.
  Parameter sigma : state -> M.t D.t.
  Parameter sigma_value : state -> V.t -> D.t.
End STORE.

Module Type TRANSFER (V : VAR) (D : DOMAIN).
  Parameter rhs observation : Type.
  Parameter observed_sides : observation -> list (V.t * D.t).
  Parameter rhs_observes : rhs -> observation -> Prop.
  Parameter rhs_eval_with : (V.t -> option D.t) ->
    rhs -> D.t -> list (V.t * D.t) -> list (V.t * D.t) -> Prop.
  Parameter rhs_dependencies_monotone rhs_effects_monotone : rhs -> Prop.
End TRANSFER.

(** Shared statement vocabulary; no solver proof or update laws are needed. *)
Module Make (V : VAR) (D : DOMAIN) (M : MAP V)
  (Transfer : TRANSFER V D)
  (R : STORE V D M).

  Definition monotonic_system (tf : V.t -> Transfer.rhs) : Prop := forall owner,
    Transfer.rhs_dependencies_monotone (tf owner) /\
    Transfer.rhs_effects_monotone (tf owner).

  (** Spawns are allowed; only side contributions are excluded. *)
  Definition no_side_effects (tf : V.t -> Transfer.rhs) : Prop :=
    forall owner result, Transfer.rhs_observes (tf owner) result ->
      Transfer.observed_sides result = nil.

  Definition solved (final : R.state) (owner : V.t) : Prop :=
    exists value, M.lookup (R.sigma final) owner = Some value.

  Definition replay (final : R.state) :=
    Transfer.rhs_eval_with (fun target => M.lookup (R.sigma final) target).

  Definition owner_post_solution (tf : V.t -> Transfer.rhs)
    (final : R.state) (owner : V.t) : Prop :=
    forall direct reads effects, replay final (tf owner) direct reads effects ->
      D.leq direct (R.sigma_value final owner) = true /\
      (forall target value, In (target,value) effects ->
        D.leq value (R.sigma_value final target) = true).

  Definition correct_final_state (tf : V.t -> Transfer.rhs)
    (roots : list V.t) (final : R.state) : Prop :=
    forall owner, In owner roots ->
      solved final owner /\ owner_post_solution tf final owner.

  (** Replay existence rules out vacuous fixedness on an incomplete store.
      [input] selects the direct result or includes incoming contributions. *)
  Definition narrowing_fixed_with (narrow : D.t -> D.t -> D.t)
    (input : R.state -> V.t -> D.t -> D.t)
    (tf : V.t -> Transfer.rhs) (final : R.state) : Prop :=
    forall owner, solved final owner ->
      (exists direct reads effects, replay final (tf owner) direct reads effects) /\
      (forall direct reads effects, replay final (tf owner) direct reads effects ->
        let value := R.sigma_value final owner in
        let narrowed := narrow value (input final owner direct) in
        D.leq narrowed value = true /\ D.leq value narrowed = true).
End Make.
