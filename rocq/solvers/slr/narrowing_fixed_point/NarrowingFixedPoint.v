From Stdlib Require Import List Bool Arith.PeanoNat.
From TcSolvers Require Export solvers.slr.narrowing_fixed_point.Base.
From TcSolvers Require Import common.Assumptions.
Import ListNotations.
Set Implicit Arguments.

(** Batched side publication, commit suspension, and source repair extend
    the core machine. Execution is independent of the proof modules. *)
Module Type CORE (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Ranks : DISCOVERY_ORDER V) (Features : Base.FEATURES).
  Include Base.Make V D U S M Ranks Features.
End CORE.

Module WithCore (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Ranks : DISCOVERY_ORDER V) (Features : Base.FEATURES)
  (R : CORE V D U S M Ranks Features).
  Definition pending_above (st : R.state) (owner : V.t) :=
    if S.mem owner (R.controlled st) then
      match R.queue_pop (R.queue st) with
      | Some (target, rest) =>
          if R.rank_lt st owner target then Some (target, rest) else None
      | None => None
      end
    else None.

  Definition suspend_commit (tf : R.ConstraintSystem.system)
    (st : R.state) (fr : R.frame) (k : R.continuation)
    (target : V.t) (rest : R.work_queue) : R.config :=
    {| R.cfg_state := R.with_queue st rest;
       R.cfg_control := R.StartEpisode target
         (R.KAfterSide
           (R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr))
           (tf (R.frame_owner fr)) k) |}.

  Definition next_precommit (tf : R.ConstraintSystem.system) (c : R.config) :=
    match R.cfg_control c with
    | R.RunCommit fr direct k =>
        match pending_above (R.cfg_state c) (R.frame_owner fr) with
        | Some (target, rest) =>
            Some (suspend_commit tf (R.cfg_state c) fr k target rest)
        | None => R.next_config tf c
        end
    | _ => R.next_config tf c
    end.

  Fixpoint publish_accumulated (targets : list V.t) (st : R.state) (fr : R.frame) :=
    match targets with
    | [] => st
    | target :: rest =>
        let input := match M.lookup (R.frame_local_side fr) target with
          | Some value => value | None => D.bottom end in
        let '(next, changed) := R.write_side_contribution st fr target input in
        publish_accumulated rest (if changed then R.enqueue next target else next) fr
    end.

  Definition next_batched (tf : R.ConstraintSystem.system) (c : R.config) :=
    let st := R.cfg_state c in
    match R.cfg_control c with
    | R.RunRhs fr (R.ConstraintSystem.Side target raw body) k =>
        let '(next_fr, _) := R.record_side_input fr target raw in
        Some {| R.cfg_state := R.observe st target;
                R.cfg_control := R.RunRhs next_fr body k |}
    | R.RunDead fr direct [] k =>
        let next := publish_accumulated (S.elements (R.frame_current_targets fr)) st fr in
        Some {| R.cfg_state := R.publish_targets next fr;
                R.cfg_control := R.RunCommit fr direct k |}
    | _ => next_precommit tf c
    end.

  Definition clear_owner (st : R.state) (owner : V.t) :=
    R.with_queue st
      (List.filter (fun x => if V.eq_dec x owner then false else true) (R.queue st)).

  Definition retry_current (tf : R.ConstraintSystem.system)
    (st : R.state) (fr : R.frame) (k : R.continuation) : R.config :=
    let current := clear_owner st (R.frame_owner fr) in
    {| R.cfg_state := current;
       R.cfg_control := R.RunRhs
         (R.fresh_frame current (R.frame_owner fr) (R.frame_phase fr))
         (tf (R.frame_owner fr)) k |}.

  Definition next_fresh (tf : R.ConstraintSystem.system) (c : R.config) :=
    let st := R.cfg_state c in
    match R.cfg_control c with
    | R.StartEpisode owner k =>
        next_batched tf {| R.cfg_state := clear_owner st owner;
                           R.cfg_control := R.StartEpisode owner k |}
    | R.Return (R.KAfterSide fr body k) =>
        next_batched tf {| R.cfg_state := clear_owner st (R.frame_owner fr);
                           R.cfg_control := R.Return (R.KAfterSide fr body k) |}
    | R.RunCommit fr direct k =>
        match pending_above st (R.frame_owner fr) with
        | Some (target, rest) => Some (suspend_commit tf st fr k target rest)
        | None =>
            if R.queue_contains (R.frame_owner fr) (R.queue st)
            then Some (retry_current tf st fr k)
            else next_batched tf c
        end
    | _ => next_batched tf c
    end.

  Definition cell_changed before after source target :=
    negb (R.equivalent (R.stored_contribution before source target)
      (R.stored_contribution after source target)).

  Definition requeue_source before after source target :=
    if cell_changed before after source target then R.enqueue after source else after.

  Definition finish_write before after fr target (aggregate_changed : bool) :=
    let next := requeue_source before after (R.frame_owner fr) target in
    if aggregate_changed then R.enqueue next target else next.

  Fixpoint publish (targets : list V.t) (st : R.state) (fr : R.frame) :=
    match targets with
    | [] => st
    | target :: rest =>
        let input := match M.lookup (R.frame_local_side fr) target with
          Some value => value | None => D.bottom end in
        let '(next, changed) := R.write_side_contribution st fr target input in
        publish rest (finish_write st next fr target changed) fr
    end.

  Definition next_repaired tf (c : R.config) :=
    let st := R.cfg_state c in
    match R.cfg_control c with
    | R.RunDead fr direct [] k =>
        Some {| R.cfg_state := R.publish_targets
          (publish (S.elements (R.frame_current_targets fr)) st fr) fr;
          R.cfg_control := R.RunCommit fr direct k |}
    | R.RunDead fr direct (target :: rest) k =>
        if S.mem target (R.frame_current_targets fr) then
          Some {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct rest k |}
        else let '(next, changed) := R.write_side_contribution st fr target D.bottom in
          Some (R.continue_dead (requeue_source st next (R.frame_owner fr) target)
            fr direct target rest k changed)
    | _ => next_fresh tf c
    end.

  Definition next_config tf (c : R.config) :=
    match R.cfg_control c with
    | R.Return (R.KAfterSide fr body k) =>
        match pending_above (R.cfg_state c) (R.frame_owner fr) with
        | Some (target, rest) =>
            Some (suspend_commit tf (R.cfg_state c) fr k target rest)
        | None => next_repaired tf c
        end
    | _ => next_repaired tf c
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
  | steps_next : forall before next after,
      next_config tf before = Some next -> steps tf next after -> steps tf before after.

  Lemma fuel_steps fuel tf c : steps tf c (run_fuel fuel tf c).
  Proof.
    revert c; induction fuel as [|fuel IH]; intro c; cbn; [constructor |].
    destruct (next_config tf c) as [next|] eqn:Hstep;
      [econstructor; [exact Hstep |apply IH] |constructor].
  Qed.
End WithCore.

Module Runtime (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES).
  Module Ranks := ListDiscoveryOrder V.
  Module R := Base.Make V D U S M Ranks Features.
  Include WithCore V D U S M Ranks Features R.
End Runtime.

(** The law-parameterized interface shares the executable [Runtime]. *)
Module Make (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Include Runtime V D U S M Features.
End Make.
