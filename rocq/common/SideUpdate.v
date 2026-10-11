From TcSolvers Require Import
  common.Interfaces
  common.Assumptions.

Set Implicit Arguments.

(** Aggregate-aware side-update interface shared by second-paper solvers. *)
Module Type SIDE_UPDATE (V : VAR) (D : DOMAIN).
  Parameter phase : Type.
  Parameter initial_phase : V.t -> V.t -> phase.
  Parameter update :
    V.t -> V.t -> phase -> D.t -> D.t -> D.t -> phase * D.t.
End SIDE_UPDATE.

Module Type ORDINARY_UPDATE_SOUND_LAWS
  (V : VAR) (D : DOMAIN) (U : UPDATE V D).
  Parameter update_sound :
    forall variable phase old input,
      D.leq input (snd (U.update false variable phase old input)) = true.
End ORDINARY_UPDATE_SOUND_LAWS.

Module Type SIDE_UPDATE_SOUND_LAWS
  (V : VAR) (D : DOMAIN) (SU : SIDE_UPDATE V D).
  Parameter update_sound :
    forall source target phase old input aggregate,
      D.leq input
        (snd (SU.update source target phase old input aggregate)) = true.
End SIDE_UPDATE_SOUND_LAWS.

(** Leastness needs side updates to preserve every common upper bound. *)
Module Type SIDE_UPPER_BOUND_UPDATE_LAWS
  (V : VAR) (D : DOMAIN) (SU : SIDE_UPDATE V D).
  Parameter update_preserves_upper_bound :
    forall source target phase old input aggregate upper,
      D.leq old upper = true ->
      D.leq input upper = true ->
      D.leq
        (snd (SU.update source target phase old input aggregate))
        upper = true.
End SIDE_UPPER_BOUND_UPDATE_LAWS.

Module Type ORDINARY_UPDATE_TERMINATION_LAWS
  (V : VAR) (D : DOMAIN) (U : UPDATE V D).

  Include ORDINARY_UPDATE_SOUND_LAWS V D U.

  Definition equivalent (left right : D.t) : Prop :=
    D.leq left right = true /\ D.leq right left = true.

  Parameter remaining_changes : U.phase -> D.t -> nat.

  Parameter remaining_changes_extensional :
    forall phase old old',
      equivalent old old' ->
      remaining_changes phase old = remaining_changes phase old'.

  Parameter remaining_changes_nonincreasing :
    forall variable phase old input,
      remaining_changes
        (fst (U.update false variable phase old input))
        (snd (U.update false variable phase old input)) <=
      remaining_changes phase old.

  Parameter update_change_consumes :
    forall variable phase old input,
      ~ equivalent
          (snd (U.update false variable phase old input)) old ->
      remaining_changes
        (fst (U.update false variable phase old input))
        (snd (U.update false variable phase old input)) <
      remaining_changes phase old.
End ORDINARY_UPDATE_TERMINATION_LAWS.

Module Type SIDE_UPDATE_TERMINATION_LAWS
  (V : VAR) (D : DOMAIN) (SU : SIDE_UPDATE V D).

  Include SIDE_UPDATE_SOUND_LAWS V D SU.

  Definition equivalent (left right : D.t) : Prop :=
    D.leq left right = true /\ D.leq right left = true.

  Parameter remaining_changes : SU.phase -> D.t -> nat.

  Parameter remaining_changes_extensional :
    forall phase old old',
      equivalent old old' ->
      remaining_changes phase old = remaining_changes phase old'.

  Parameter remaining_changes_nonincreasing :
    forall source target phase old input aggregate,
      D.leq old aggregate = true ->
      remaining_changes
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) <=
      remaining_changes phase old.

  Parameter exposed_change_consumes :
    forall source target phase old input aggregate,
      D.leq old aggregate = true ->
      D.leq
        (snd (SU.update source target phase old input aggregate))
        aggregate = false ->
      remaining_changes
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) <
      remaining_changes phase old.
End SIDE_UPDATE_TERMINATION_LAWS.

(** The extra constructive obligation needed when a base update is replaced
    by an aggregate-covered join. *)
Module Type COVERED_JOIN_CREDIT_LAWS
  (V : VAR) (D : DOMAIN) (Base : UPDATE V D)
  (BaseLaws : UPDATE_LAWS V D Base).
  Parameter covered_join_nonincreasing :
    forall target phase old input aggregate,
      D.leq old aggregate = true ->
      D.leq input old = false ->
      D.leq input aggregate = true ->
      BaseLaws.remaining_changes
        (fst (Base.update true target phase old input))
        (D.join old input) <=
      BaseLaws.remaining_changes phase old.
End COVERED_JOIN_CREDIT_LAWS.

(** Existing update contracts remain usable for ordinary values. *)
Module OrdinaryUpdateSoundAdapter
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (UL : UPDATE_LAWS V D U).
  Definition update_sound :
    forall variable phase old input,
      D.leq input (snd (U.update false variable phase old input)) = true :=
    fun variable phase old input =>
      UL.update_sound false variable phase old input.
End OrdinaryUpdateSoundAdapter.

Module OrdinaryUpdateTerminationAdapter
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (UL : UPDATE_LAWS V D U).

  Include OrdinaryUpdateSoundAdapter V D U UL.

  Definition equivalent := UL.equivalent.
  Definition remaining_changes := UL.remaining_changes.
  Definition remaining_changes_extensional :=
    UL.remaining_changes_extensional.

  Definition remaining_changes_nonincreasing :
    forall variable phase old input,
      remaining_changes
        (fst (U.update false variable phase old input))
        (snd (U.update false variable phase old input)) <=
      remaining_changes phase old :=
    fun variable phase old input =>
      UL.remaining_changes_nonincreasing false variable phase old input.

  Definition update_change_consumes :
    forall variable phase old input,
      ~ equivalent (snd (U.update false variable phase old input)) old ->
      remaining_changes
        (fst (U.update false variable phase old input))
        (snd (U.update false variable phase old input)) <
      remaining_changes phase old :=
    fun variable phase old input Hchange =>
      @UL.update_change_consumes false variable phase old input Hchange.
End OrdinaryUpdateTerminationAdapter.
