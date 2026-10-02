From Stdlib Require Import List.
From TcSolvers Require Import
  common.Assumptions.

Set Implicit Arguments.

(** A semantic assumption for leastness only. Non-strict initializers belong
    to [roots]. Bottom means domain equivalence to bottom, not Leibniz equality.
    Parameterizing the observation interface avoids generating new trace
    types when this argument is instantiated for a solver. *)
Module Make
  (V : VAR) (D : DOMAIN) (DL : DOMAIN_LAWS D).

  Section Constraints.
  Context {rhs observation : Type}.
  Variable observes_at : (V.t -> D.t) -> rhs -> observation -> Prop.
  Variable observed_direct : observation -> D.t.
  Variable observed_sides : observation -> list (V.t * D.t).

  Definition side_effects_below (values : V.t -> D.t)
    (effects : list (V.t * D.t)) : Prop :=
    forall target value, List.In (target, value) effects ->
      D.leq value (values target) = true.

  (** Numerical satisfaction only; callers separately establish spawn closure. *)
  Definition value_post_solution_on
    (tf : V.t -> rhs) (support : list V.t) (values : V.t -> D.t) : Prop :=
    forall owner, List.In owner support ->
    forall result, observes_at values (tf owner) result ->
      D.leq (observed_direct result) (values owner) = true /\
      side_effects_below values (observed_sides result).

  Definition source_strict_on
    (tf : V.t -> rhs) (support roots : list V.t) : Prop :=
    forall owner, List.In owner support -> ~ List.In owner roots ->
    forall values result,
      observes_at values (tf owner) result ->
      D.leq (values owner) D.bottom = true ->
      D.leq (observed_direct result) D.bottom = true /\
      side_effects_below (fun _ => D.bottom) (observed_sides result).

  Lemma source_strict_on_all_roots : forall tf support,
    source_strict_on tf support support.
  Proof. intros tf support owner Hin Hnotin. contradiction. Qed.

  (** Unsolved constraints are harmless under source strictness. The caller
      proves solvedness and local satisfaction from the solver invariants. *)
  Lemma bottom_completion_is_value_post_solution :
    forall tf support roots values (solved : V.t -> Prop),
      (forall x, {solved x} + {~ solved x}) ->
      source_strict_on tf support roots ->
      (forall x, List.In x roots -> solved x) ->
      (forall x, ~ solved x -> D.leq (values x) D.bottom = true) ->
      (forall owner, List.In owner support -> solved owner ->
        forall result, observes_at values (tf owner) result ->
        D.leq (observed_direct result) (values owner) = true /\
        side_effects_below values (observed_sides result)) ->
      value_post_solution_on tf support values.
  Proof.
    intros tf support roots values solved Hdec Hstrict Hroots Hbottom Hlocal
      owner Hin result Hobs.
    destruct (Hdec owner) as [Hsolved | Hunsolved].
    - exact (Hlocal owner Hin Hsolved result Hobs).
    - assert (Hnotroot : ~ List.In owner roots).
      { intro Hroot. apply Hunsolved. now apply Hroots. }
      destruct (Hstrict owner Hin Hnotroot values result Hobs
        (Hbottom owner Hunsolved)) as [Hdirect Hsides].
      split.
      + eapply DL.leq_trans; [exact Hdirect |apply DL.bottom_least].
      + intros target value Hside.
        eapply DL.leq_trans; [exact (Hsides target value Hside) |
          apply DL.bottom_least].
  Qed.
  End Constraints.
End Make.
