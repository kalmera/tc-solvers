From Stdlib Require Import List Bool Arith.PeanoNat.
From TcSolvers Require Import common.Assumptions
  solvers.slr.narrowing_fixed_point.Base
  solvers.slr.narrowing_fixed_point.proofs.AccumulatedReplay.
Import ListNotations.
Set Implicit Arguments.

(** At a precommit child return, drain remaining higher work before replaying
    the suspended source. This has its own execution; Replay
    and Theorems prove its termination and fixedness. *)
Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module O := AccumulatedReplay.Make V D U S M Features DL UL SL ML.
  Module C := O.PS.C.
  Module P := C.P.
  Module R := C.R.
  Module B := C.H.B.
  Module H := C.H.

  Definition next_config tf (c : R.config) :=
    match R.cfg_control c with
    | R.Return (R.KAfterSide fr body k) =>
        match P.pending_above (R.cfg_state c) (R.frame_owner fr) with
        | Some (target, rest) =>
            Some (P.suspend_commit tf (R.cfg_state c) fr k target rest)
        | None => C.next_config tf c
        end
    | _ => C.next_config tf c
    end.

  Fixpoint run_fuel fuel tf c :=
    match fuel with
    | 0 => c
    | S fuel => match next_config tf c with
        Some next => run_fuel fuel tf next | None => c end
    end.
  Definition solve_fuel fuel tf roots :=
    R.terminal_state (run_fuel fuel tf (R.initial_config roots)).

  Inductive steps tf : R.config -> R.config -> Prop :=
  | steps_refl : forall c, steps tf c c
  | steps_next : forall first next last,
      next_config tf first = Some next -> steps tf next last -> steps tf first last.

  Lemma fuel_steps fuel tf c : steps tf c (run_fuel fuel tf c).
  Proof.
    revert c. induction fuel as [|fuel IH]; intro c; cbn; [constructor |].
    destruct (next_config tf c) as [next|] eqn:Hstep;
      [econstructor; [exact Hstep |apply IH] |constructor].
  Qed.

  Lemma resume_higher tf st fr body k target rest :
    P.pending_above st (R.frame_owner fr) = Some (target, rest) ->
    next_config tf {|R.cfg_state := st;
      R.cfg_control := R.Return (R.KAfterSide fr body k)|} =
      Some (P.suspend_commit tf st fr k target rest).
  Proof. intro Hpending. cbn -[P.pending_above P.suspend_commit]. now rewrite Hpending. Qed.

  Lemma resume_ready tf st fr body k :
    P.pending_above st (R.frame_owner fr) = None ->
    next_config tf {|R.cfg_state := st;
      R.cfg_control := R.Return (R.KAfterSide fr body k)|} =
    C.next_config tf {|R.cfg_state := st;
      R.cfg_control := R.Return (R.KAfterSide fr body k)|}.
  Proof. intro Hpending. cbn -[P.pending_above C.next_config]. now rewrite Hpending. Qed.

  Lemma resume_history tf st fr body k target rest :
    P.pending_above st (R.frame_owner fr) = Some (target, rest) ->
    H.valid tf {|R.cfg_state := st;
      R.cfg_control := R.Return (R.KAfterSide fr body k)|} ->
    H.valid tf (P.suspend_commit tf st fr k target rest).
  Proof.
    intros Hpending [Ho [Hbody Hk]].
    destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hpending)
      as [_ [Hpop Hlt]].
    split; cbn.
    - split; [exact Hlt |]. eapply H.below_extended;
        [apply B.rank_extends_with_queue |exact Ho].
    - split; [reflexivity |]. eapply H.continuation_pop;
        [exact Hpop |exact Ho |now right |exact Hk].
  Qed.

  Lemma next_history tf before after :
    H.valid tf before -> next_config tf before = Some after -> H.valid tf after.
  Proof.
    destruct before as [st control]. intros Hvalid Hstep.
    destruct control; cbn -[C.next_config P.pending_above P.suspend_commit] in Hstep;
      try solve [eapply C.next_history; eauto].
    destruct c; cbn -[C.next_config P.pending_above P.suspend_commit] in Hstep;
      try solve [eapply C.next_history; eauto].
    destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
    - inversion Hstep; subst. eapply resume_history; eauto.
    - eapply C.next_history; eauto.
  Qed.

  Theorem reachable_history tf roots c : steps tf (R.initial_config roots) c ->
    H.valid tf c.
  Proof.
    assert (Hpreserve : forall first last, steps tf first last ->
      H.valid tf first -> H.valid tf last).
    { intros first last Hsteps. induction Hsteps; intro Hvalid; [exact Hvalid |].
      apply IHHsteps. eapply next_history; eauto. }
    intro Hsteps. eapply Hpreserve; [exact Hsteps |]. split; exact I.
  Qed.

  Theorem actual_commit_replay tf roots st fr direct k after next_fr next_k :
    steps tf (R.initial_config roots)
      {|R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k|} ->
    next_config tf {|R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k|} =
      Some {|R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k|} ->
    exists reads effects, B.Sem.rhs_eval st (tf (R.frame_owner fr)) direct reads effects.
  Proof.
    intros Hreach Hstep.
    destruct (reachable_history Hreach) as [_ [[reads [effects [Htrace Hguard]]] _]].
    destruct (@P.fresh_commit_ready tf st fr direct k after next_fr next_k Hstep)
      as [_ Hclean].
    exists reads, effects. apply B.rhs_trace_replay; [exact Htrace |].
    eapply H.guarded_reads_clean; eauto.
  Qed.

  Lemma resume_scopes tf st fr body k target rest :
    B.ScopeBounds.scopes_bounded {|R.cfg_state := st;
      R.cfg_control := R.Return (R.KAfterSide fr body k)|} ->
    B.ScopeBounds.scopes_bounded (P.suspend_commit tf st fr k target rest).
  Proof.
    intro Hscopes. apply (@P.suspend_scopes tf st fr D.bottom k target rest).
    exact Hscopes.
  Qed.

  Lemma next_scopes tf before after :
    B.ScopeBounds.scopes_bounded before -> next_config tf before = Some after ->
    B.ScopeBounds.scopes_bounded after.
  Proof.
    destruct before as [st control]. intros Hscopes Hstep.
    destruct control; cbn -[C.next_config P.pending_above P.suspend_commit] in Hstep;
      try solve [eapply C.next_scopes; eauto].
    destruct c; cbn -[C.next_config P.pending_above P.suspend_commit] in Hstep;
      try solve [eapply C.next_scopes; eauto].
    destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
    - inversion Hstep; subst. eapply resume_scopes; exact Hscopes.
    - eapply C.next_scopes; eauto.
  Qed.

  Theorem reachable_scopes tf roots c : steps tf (R.initial_config roots) c ->
    B.ScopeBounds.scopes_bounded c.
  Proof.
    assert (Hpreserve : forall first last, steps tf first last ->
      B.ScopeBounds.scopes_bounded first -> B.ScopeBounds.scopes_bounded last).
    { intros first last Hsteps. induction Hsteps; intro Hscopes; [exact Hscopes |].
      apply IHHsteps. eapply next_scopes; eauto. }
    intro Hsteps. eapply Hpreserve; [exact Hsteps |].
    apply B.ScopeBounds.reachable_scopes_bounded with tf roots. constructor.
  Qed.

  Theorem higher_reset_preserves_credit tf roots c support source scope :
    steps tf (R.initial_config roots) c -> R.rank_lt (R.cfg_state c) source scope = true ->
    B.Credits.source_side_credit support
      (R.reset_registered_cells (R.cfg_state c) scope) source =
    B.Credits.source_side_credit support (R.cfg_state c) source.
  Proof.
    intros Hsteps Hrank. apply B.reset_above_preserves_source_credit;
      [exact (proj1 (reachable_scopes Hsteps)) |exact Hrank].
  Qed.
End Make.
