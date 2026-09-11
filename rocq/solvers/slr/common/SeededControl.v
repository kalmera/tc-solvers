From Stdlib Require Import List.
From TcSolvers Require Export solvers.slr.common.Monadic.

Import ListNotations.
Set Implicit Arguments.

(** Relational specification of the delayed seed driver, instantiated with
    an ordinary functional state monad.  The relations make the sequencing
    guarantee explicit: solve a fresh seed, drain its queue, then inspect the
    next seed. *)
Module StateSeedDriver.
  Section Driver.
    Context {V State : Type}.

    Definition StateM (A : Type) : Type := State -> A * State.

    Definition ret {A : Type} (value : A) : StateM A :=
      fun st => (value, st).

    Definition bind {A B : Type}
        (action : StateM A) (next : A -> StateM B) : StateM B :=
      fun st =>
        let '(value, after) := action st in
        next value after.

    Context
      (is_started : V -> StateM bool)
      (pop_owner : unit -> StateM (option V))
      (solve_owner : V -> StateM unit).

    Definition run_drain (fuel : nat) :
        StateM Monadic.seeded_result :=
      @Monadic.drain_with_fuel V StateM (@ret) (@bind)
        fuel pop_owner solve_owner.

    Definition run_seeds (fuel : nat) (roots : list V) :
        StateM Monadic.seeded_result :=
      @Monadic.solve_seeds_with_fuel V StateM (@ret) (@bind)
        fuel is_started pop_owner solve_owner roots.

    Inductive drains :
      nat -> State -> Monadic.seeded_result -> State -> Prop :=
    | DrainsEmpty :
        forall fuel before after,
          pop_owner tt before = (None, after) ->
          drains fuel before (Monadic.SeedsSolved fuel) after
    | DrainsNoFuel :
        forall before popped owner,
          pop_owner tt before = (Some owner, popped) ->
          drains 0 before Monadic.SeedsOutOfFuel popped
    | DrainsOwner :
        forall fuel before popped owner solved result after,
          pop_owner tt before = (Some owner, popped) ->
          solve_owner owner popped = (tt, solved) ->
          drains fuel solved result after ->
          drains (S fuel) before result after.

    Inductive seeds :
      nat -> list V -> State ->
      Monadic.seeded_result -> State -> Prop :=
    | SeedsDone :
        forall fuel before,
          seeds fuel [] before
            (Monadic.SeedsSolved fuel) before
    | SeedsAlreadyStarted :
        forall fuel root roots before checked result after,
          is_started root before = (true, checked) ->
          seeds fuel roots checked result after ->
          seeds fuel (root :: roots) before result after
    | SeedsFreshNoFuel :
        forall root roots before checked,
          is_started root before = (false, checked) ->
          seeds 0 (root :: roots) before
            Monadic.SeedsOutOfFuel checked
    | SeedsFreshDrainFailed :
        forall fuel root roots before checked solved drained,
          is_started root before = (false, checked) ->
          solve_owner root checked = (tt, solved) ->
          drains fuel solved Monadic.SeedsOutOfFuel drained ->
          seeds (S fuel) (root :: roots) before
            Monadic.SeedsOutOfFuel drained
    | SeedsFresh :
        forall fuel after_drain root roots before checked solved drained
          result after,
          is_started root before = (false, checked) ->
          solve_owner root checked = (tt, solved) ->
          drains fuel solved
            (Monadic.SeedsSolved after_drain) drained ->
          seeds after_drain roots drained result after ->
          seeds (S fuel) (root :: roots) before result after.

    Lemma run_drain_sound :
      forall fuel before result after,
        run_drain fuel before = (result, after) ->
        drains fuel before result after.
    Proof.
      induction fuel as [|fuel IH]; intros before result after Hrun;
        unfold run_drain in Hrun; cbn in Hrun;
        destruct (pop_owner tt before) as [[owner |] popped] eqn:Hpop.
      - unfold bind in Hrun. rewrite Hpop in Hrun. cbn in Hrun.
        inversion Hrun; subst. eapply DrainsNoFuel. exact Hpop.
      - unfold bind in Hrun. rewrite Hpop in Hrun. cbn in Hrun.
        inversion Hrun; subst. eapply DrainsEmpty. exact Hpop.
      - destruct (solve_owner owner popped) as [[] solved] eqn:Hsolve.
        unfold bind in Hrun. rewrite Hpop in Hrun. cbn in Hrun.
        unfold bind in Hrun. rewrite Hsolve in Hrun. cbn in Hrun.
        eapply DrainsOwner; [exact Hpop | exact Hsolve |].
        apply IH. exact Hrun.
      - unfold bind in Hrun. rewrite Hpop in Hrun. cbn in Hrun.
        inversion Hrun; subst. eapply DrainsEmpty. exact Hpop.
    Qed.

    Lemma run_seeds_sound :
      forall roots fuel before result after,
        run_seeds fuel roots before = (result, after) ->
        seeds fuel roots before result after.
    Proof.
      induction roots as [|root roots IH]; intros fuel before result after Hrun.
      - inversion Hrun; subst. constructor.
      - unfold run_seeds in Hrun. cbn in Hrun.
        destruct (is_started root before) as [[|] checked] eqn:Hstarted.
        + unfold bind in Hrun. rewrite Hstarted in Hrun. cbn in Hrun.
          eapply SeedsAlreadyStarted; [exact Hstarted |].
          apply IH. exact Hrun.
        + destruct fuel as [|fuel].
          * unfold bind in Hrun. rewrite Hstarted in Hrun. cbn in Hrun.
            inversion Hrun; subst. now apply SeedsFreshNoFuel.
          * destruct (solve_owner root checked) as [[] solved] eqn:Hsolve.
            unfold bind in Hrun. rewrite Hstarted in Hrun. cbn in Hrun.
            unfold bind in Hrun. rewrite Hsolve in Hrun. cbn in Hrun.
            remember (run_drain fuel solved) as drained_run eqn:Hdrain.
            change
              (bind (run_drain fuel)
                (fun drained =>
                  match drained with
                  | Monadic.SeedsSolved after_drain =>
                      run_seeds after_drain roots
                  | Monadic.SeedsOutOfFuel =>
                      ret Monadic.SeedsOutOfFuel
                  end) solved = (result, after)) in Hrun.
            unfold bind in Hrun. rewrite <- Hdrain in Hrun. cbn in Hrun.
            destruct drained_run as [[after_drain |] drained].
            -- eapply SeedsFresh; [exact Hstarted | exact Hsolve | |].
               ++ eapply run_drain_sound. symmetry. exact Hdrain.
               ++ apply IH. exact Hrun.
            -- inversion Hrun; subst.
               eapply SeedsFreshDrainFailed;
                 [exact Hstarted | exact Hsolve |].
               eapply run_drain_sound. symmetry. exact Hdrain.
    Qed.
  End Driver.
End StateSeedDriver.
