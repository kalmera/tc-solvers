From Stdlib Require Import Lia.
From TcSolvers Require Import
  common.Assumptions
  common.BoxUpdate.

Set Implicit Arguments.

(** Constructive sequence and quantitative forms of strong widening. *)
Module StrongWidening.

Module Make
  (D : DOMAIN)
  (WN : WIDEN_NARROW D)
  (DL : DOMAIN_LAWS D).

  Definition widened (old input : D.t) : D.t :=
    WN.widen old input.

  Definition increasing (values : nat -> D.t) : Prop :=
    forall i, D.leq (values i) (values (S i)) = true.

  Definition widening_subsumed
    (values inputs : nat -> D.t) : Prop :=
    forall i, D.leq (widened (values i) (inputs i))
      (values (S i)) = true.

  Definition eventually_covered
    (values inputs : nat -> D.t) : Prop :=
    exists first, forall i, first <= i ->
      D.leq (inputs i) (values i) = true.

  (** Definition 4.1's sequence clause, separated from its algebraic
      upper-bound and stuttering requirements. *)
  Definition paper_sequence_property : Prop :=
    forall values inputs,
      increasing values ->
      widening_subsumed values inputs ->
      eventually_covered values inputs.

  Definition frequently_uncovered
    (values inputs : nat -> D.t) : Prop :=
    forall first, exists i, first <= i /\
      D.leq (inputs i) (values i) = false.

  (** This is the contradiction form used in the paper's termination proof.
      It is constructively weaker than producing an eventual-stability index. *)
  Definition no_frequent_uncovered : Prop :=
    forall values inputs,
      increasing values ->
      widening_subsumed values inputs ->
      ~ frequently_uncovered values inputs.

  Lemma leq_sequence :
    forall values,
      increasing values ->
      forall first last, first <= last ->
      D.leq (values first) (values last) = true.
  Proof.
    intros values Hincreasing first last Hle.
    induction Hle.
    - apply DL.leq_refl.
    - eapply DL.leq_trans; [exact IHHle |apply Hincreasing].
  Qed.

  Lemma paper_sequence_property_no_frequent :
    paper_sequence_property -> no_frequent_uncovered.
  Proof.
    intros Hpaper values inputs Hincreasing Hsubsumed Hfrequent.
    destruct (Hpaper values inputs Hincreasing Hsubsumed)
      as [first Hcovered].
    destruct (Hfrequent first) as [i [Hfirst Huncovered]].
    rewrite (Hcovered i Hfirst) in Huncovered. discriminate.
  Qed.

  Module Type QUANTITATIVE_STRONG_WIDENING.
    Parameter remaining : D.t -> nat.

    Parameter remaining_antitone :
      forall old next,
        D.leq old next = true -> remaining next <= remaining old.

    Parameter uncovered_widening_consumes :
      forall old input next,
        D.leq input old = false ->
        D.leq (widened old input) next = true ->
        remaining next < remaining old.
  End QUANTITATIVE_STRONG_WIDENING.

  Module QuantitativeBridge (Q : QUANTITATIVE_STRONG_WIDENING).

    Lemma consume_after_delay :
      forall values inputs,
        increasing values ->
        widening_subsumed values inputs ->
        forall first i,
          first <= i ->
          D.leq (inputs i) (values i) = false ->
          Q.remaining (values (S i)) < Q.remaining (values first).
    Proof.
      intros values inputs Hincreasing Hsubsumed first i Hfirst Huncovered.
      pose proof (@Q.remaining_antitone (values first) (values i)
        (@leq_sequence values Hincreasing first i Hfirst)) as Hdelay.
      pose proof (@Q.uncovered_widening_consumes
        (values i) (inputs i) (values (S i))
        Huncovered (Hsubsumed i)) as Hconsume.
      lia.
    Qed.

    Lemma arbitrarily_many_consumptions :
      forall values inputs,
        increasing values ->
        widening_subsumed values inputs ->
        frequently_uncovered values inputs ->
        forall count first,
          exists last,
            first <= last /\
            Q.remaining (values last) + count <=
              Q.remaining (values first).
    Proof.
      intros values inputs Hincreasing Hsubsumed Hfrequent count.
      induction count as [|count IH]; intros first.
      - exists first. split; lia.
      - destruct (Hfrequent first) as [i [Hfirst Huncovered]].
        destruct (IH (S i)) as [last [Hilast Hcredit]].
        exists last. split; [lia |].
        pose proof (@consume_after_delay values inputs
          Hincreasing Hsubsumed first i Hfirst Huncovered) as Hconsume.
        pose proof (@Q.remaining_antitone (values (S i)) (values last)
          (@leq_sequence values Hincreasing (S i) last Hilast)) as Htail.
        lia.
    Qed.

    Theorem quantitative_no_frequent_uncovered : no_frequent_uncovered.
    Proof.
      intros values inputs Hincreasing Hsubsumed Hfrequent.
      destruct (@arbitrarily_many_consumptions values inputs
        Hincreasing Hsubsumed Hfrequent
        (S (Q.remaining (values 0))) 0)
        as [last [_ Hcredit]].
      lia.
    Qed.
  End QuantitativeBridge.

End Make.
End StrongWidening.
