From TcSolvers Require Import
  common.Assumptions
  common.SideUpdate
  common.ReluctantUpdate.

Set Implicit Arguments.

(** Restarting must also account for shrinking side cells caused by narrowing
    and dead-side elimination.  Covered reluctant joins may retain credit;
    every changed non-covered update must consume it. *)
Module Type RESTARTING_SIDE_UPDATE_TERMINATION_LAWS
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

  Parameter covered_output_is_join :
    forall source target phase old input aggregate,
      D.leq input old = false ->
      D.leq input aggregate = true ->
      snd (SU.update source target phase old input aggregate) =
        D.join old input.

  Parameter noncovered_change_consumes :
    forall source target phase old input aggregate,
      D.leq old aggregate = true ->
      (D.leq input old = true \/ D.leq input aggregate = false) ->
      ~ equivalent
          (snd (SU.update source target phase old input aggregate)) old ->
      remaining_changes
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) <
      remaining_changes phase old.
End RESTARTING_SIDE_UPDATE_TERMINATION_LAWS.

Module ReluctantRestartingSideUpdateTerminationLaws
  (V : VAR) (D : DOMAIN) (Base : UPDATE V D)
  (DL : DOMAIN_LAWS D) (BaseLaws : UPDATE_LAWS V D Base)
  (Covered : COVERED_JOIN_CREDIT_LAWS V D Base BaseLaws).

  Module SU := ReluctantSideUpdate V D Base.
  Module Shared := ReluctantSideUpdateTerminationLaws
    V D Base DL BaseLaws Covered.

  Definition update_sound := Shared.update_sound.
  Definition equivalent := BaseLaws.equivalent.
  Definition remaining_changes := BaseLaws.remaining_changes.
  Definition remaining_changes_extensional :=
    BaseLaws.remaining_changes_extensional.
  Definition remaining_changes_nonincreasing :=
    Shared.remaining_changes_nonincreasing.

  Lemma covered_output_is_join :
    forall source target phase old input aggregate,
      D.leq input old = false ->
      D.leq input aggregate = true ->
      snd (SU.update source target phase old input aggregate) =
        D.join old input.
  Proof.
    intros source target phase old input aggregate Hinput Haggregate.
    unfold SU.update. now rewrite Hinput, Haggregate.
  Qed.

  Lemma noncovered_change_consumes :
    forall source target phase old input aggregate,
      D.leq old aggregate = true ->
      (D.leq input old = true \/ D.leq input aggregate = false) ->
      ~ equivalent
          (snd (SU.update source target phase old input aggregate)) old ->
      remaining_changes
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) <
      remaining_changes phase old.
  Proof.
    intros source target phase old input aggregate Hold Hnoncovered Hchange.
    unfold SU.update, remaining_changes, equivalent in *.
    destruct (D.leq input old) eqn:Hinput.
    - eapply BaseLaws.update_change_consumes. exact Hchange.
    - destruct (D.leq input aggregate) eqn:Haggregate.
      + destruct Hnoncovered as [Hcontra | Hcontra]; congruence.
      + eapply BaseLaws.update_change_consumes. exact Hchange.
  Qed.
End ReluctantRestartingSideUpdateTerminationLaws.
