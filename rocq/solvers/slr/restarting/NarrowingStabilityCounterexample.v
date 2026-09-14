From Stdlib Require Import List Arith.PeanoNat.
From TcSolvers Require Import
  common.Collections
  common.Assumptions
  common.BoxUpdate
  solvers.slr.restarting.Restarting.

Import ListNotations.

(** Fixed ranks permit an intermediate dependency to remain queued while a
    lower owner enters narrowing.  The dependency can then invalidate that
    owner and force OneBoxUpdate's fallback. *)
Module FixedRankFallback.

  Module V.
    Definition t := nat.
    Definition eq_dec := Nat.eq_dec.
  End V.

  Module D.
    Inductive value := Bot | One | Top.
    Definition t := value.
    Definition bottom := Bot.

    Definition leq (left right : t) : bool :=
      match left, right with
      | Bot, _ => true
      | One, Bot => false
      | One, _ => true
      | Top, Top => true
      | Top, _ => false
      end.

    Definition join (left right : t) : t :=
      match left, right with
      | Top, _ | _, Top => Top
      | One, _ | _, One => One
      | Bot, Bot => Bot
      end.
  End D.

  Module DL <: DOMAIN_LAWS D.
    Lemma leq_refl : forall x, D.leq x x = true.
    Proof. destruct x; reflexivity. Qed.

    Lemma leq_trans : forall x y z,
      D.leq x y = true -> D.leq y z = true -> D.leq x z = true.
    Proof. destruct x, y, z; cbn; congruence. Qed.

    Lemma bottom_least : forall x, D.leq D.bottom x = true.
    Proof. destruct x; reflexivity. Qed.

    Lemma join_upper_left : forall x y, D.leq x (D.join x y) = true.
    Proof. destruct x, y; reflexivity. Qed.

    Lemma join_upper_right : forall x y, D.leq y (D.join x y) = true.
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

  Module WN.
    Definition widen (_old _input : D.t) : D.t := D.Top.
    Definition narrow (_old input : D.t) : D.t := input.
  End WN.

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
    Proof. destruct old, input; reflexivity. Qed.

    Lemma narrow_upper : forall old input,
      D.leq input old = true ->
      D.leq (WN.narrow old input) old = true.
    Proof. intros old input Hle. exact Hle. Qed.
  End WNL.

  Module U := OneBoxUpdate V D WN.
  Module S := ListSet V.
  Module M := AssocMap V.

  Module Fixed.
    Definition rank (variable : V.t) : nat := variable.
  End Fixed.

  Module Features.
    Definition restart_side_phases := false.
    Definition eliminate_dead_sides := false.
  End Features.

  Module R := Restarting.FixedRank V D U S M Fixed Features.

  Definition tf (owner : V.t) : R.ConstraintSystem.rhs :=
    match owner with
    | 0 =>
        R.ConstraintSystem.Get 2 (fun payload =>
        R.ConstraintSystem.Get 0 (fun guard =>
          match guard with
          | D.Bot => R.ConstraintSystem.Ret payload
          | _ =>
              R.ConstraintSystem.Get 3 (fun child =>
                R.ConstraintSystem.Ret (D.join payload child))
          end))
    | 1 =>
        R.ConstraintSystem.Get 0 (fun _ =>
          R.ConstraintSystem.Ret D.Top)
    | 2 => R.ConstraintSystem.Ret D.One
    | 3 =>
        R.ConstraintSystem.Get 1 (fun value =>
          R.ConstraintSystem.Ret (D.join value D.One))
    | _ => R.ConstraintSystem.Ret D.Bot
    end.

  Fixpoint side_free (body : R.ConstraintSystem.rhs) : Prop :=
    match body with
    | R.ConstraintSystem.Ret _ => True
    | R.ConstraintSystem.Get _ next => forall value, side_free (next value)
    | R.ConstraintSystem.Side _ _ _ => False
    | R.ConstraintSystem.Spawn _ next => side_free next
    end.

  Example tf_is_side_free : forall owner, side_free (tf owner).
  Proof.
    intros [|[|[|[|owner]]]]; cbn; intuition; destruct value; cbn; intuition.
    all: destruct value0; cbn; intuition.
  Qed.

  Definition active_phase (c : R.config) : option U.phase :=
    match R.cfg_control c with
    | R.RunRhs fr _ _
    | R.RunDead fr _ _ _
    | R.RunCommit fr _ _
    | R.RunDrain fr _ => Some (R.frame_phase fr)
    | _ => None
    end.

  Example reaches_fallback :
    active_phase (R.run_fuel 50 tf (R.initial_config [0])) = Some U.Widen.
  Proof. vm_compute. reflexivity. Qed.

End FixedRankFallback.
