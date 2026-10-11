From Stdlib Require Import List.
From TcSolvers Require Import common.Interfaces.

Set Implicit Arguments.

(* The semantic state view used by specifications. Dormant bottom variables
   can be solved even when they have no physical map binding. *)
Module Type STORE (V : VAR) (D : DOMAIN).
  Parameter state : Type.
  (* Inline the supplied lookup when binding a view, preserving replay reduction. *)
  Parameter Inline lookup : state -> V.t -> option D.t.
  Parameter sigma_value : state -> V.t -> D.t.
End STORE.

Module Type TRANSFER (V : VAR) (D : DOMAIN).
  Parameter rhs observation : Type.
  Parameter observed_sides : observation -> list (V.t * D.t).
  Parameter observed_spawns : observation -> list V.t.
  Parameter observes_at : (V.t -> D.t) -> rhs -> observation -> Prop.
  Parameter rhs_observes : rhs -> observation -> Prop.
  Parameter rhs_eval_with : (V.t -> option D.t) ->
    rhs -> D.t -> list (V.t * D.t) -> list (V.t * D.t) -> Prop.
  Parameter rhs_dependencies_monotone rhs_effects_monotone : rhs -> Prop.
End TRANSFER.

(* Authoritative solver-independent predicates, using semantic lookup. *)
Module Make (V : VAR) (D : DOMAIN) (Transfer : TRANSFER V D)
  (R : STORE V D).
  Definition system := V.t -> Transfer.rhs.
  Definition solved final owner := exists value, R.lookup final owner = Some value.
  Definition replay final := Transfer.rhs_eval_with (R.lookup final).
  Definition side_effects_below final effects := forall target value,
    In (target, value) effects -> D.leq value (R.sigma_value final target) = true.
  Definition rhs_post_solution final owner body := forall direct reads effects,
    replay final body direct reads effects ->
    D.leq direct (R.sigma_value final owner) = true /\
    side_effects_below final effects.
  Definition owner_post_solution (tf : system) final owner :=
    (exists direct reads effects, replay final (tf owner) direct reads effects) /\
    rhs_post_solution final owner (tf owner) /\
    (forall result, Transfer.observes_at (R.sigma_value final) (tf owner) result ->
      forall target, In target (Transfer.observed_spawns result) -> solved final target).
  Definition correct_final_state (tf : system) roots final :=
    (forall owner, In owner roots -> solved final owner) /\
    (forall owner, solved final owner -> owner_post_solution tf final owner).
  Definition monotonic_system (tf : system) := forall owner,
    Transfer.rhs_dependencies_monotone (tf owner) /\ Transfer.rhs_effects_monotone (tf owner).
  Definition no_side_effects (tf : system) := forall owner result,
    Transfer.rhs_observes (tf owner) result -> Transfer.observed_sides result = nil.

  Definition narrowing_fixed_with (narrow : D.t -> D.t -> D.t)
    (input : R.state -> V.t -> D.t -> D.t) (tf : system) final :=
    forall owner, solved final owner ->
      (exists direct reads effects, replay final (tf owner) direct reads effects) /\
      (forall direct reads effects, replay final (tf owner) direct reads effects ->
        let value := R.sigma_value final owner in
        let narrowed := narrow value (input final owner direct) in
        D.leq narrowed value = true /\ D.leq value narrowed = true).
End Make.
