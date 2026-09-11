From Stdlib Require Import List.

Import ListNotations.
Set Implicit Arguments.

(** Shared public control flow for callback-based SLR-TC implementations.

    The algorithm is parameterized by a monad and by the state operations
    supplied by a solver variant. No monad laws are needed to execute it. *)
  Section Transfers.
    Context {V D : Type}.
    Context (Monad : Type -> Type).

    Definition transfer : Type :=
      (V -> Monad D) ->
      (V -> D -> Monad unit) ->
      (V -> Monad unit) ->
      Monad D.

    Definition system : Type := V -> option transfer.

    Definition eval_transfer
        (read : V -> Monad D)
        (emit : V -> D -> Monad unit)
        (spawn : V -> Monad unit)
        (body : transfer) : Monad D :=
      body read emit spawn.
  End Transfers.

  Record owner_operations
      (V D : Type)
      (Monad : Type -> Type) : Type := {
    begin_evaluation : V -> Monad unit;
    read_value : V -> V -> Monad D;
    emit_side_effect : V -> V -> D -> Monad unit;
    spawn_variable : V -> V -> Monad unit;
    commit_value : V -> D -> Monad unit;
    drain_owner : V -> Monad unit;
  }.

  Inductive solve_result : Type :=
  | Solved
  | OutOfFuel.

  (** Delayed seeding must retain unused fuel after draining one seed, so the
      following seed shares the same global bound. *)
  Inductive seeded_result : Type :=
  | SeedsSolved : nat -> seeded_result
  | SeedsOutOfFuel.

  Section Solver.
    Context {V D : Type}.
    Context (Monad : Type -> Type).
    Context (ret : forall {A : Type}, A -> Monad A).
    Context (bind :
      forall {A B : Type}, Monad A -> (A -> Monad B) -> Monad B).

    Local Notation "'let*' x ':=' action 'in' next" :=
      (bind action (fun x => next))
      (at level 200, x pattern, action at level 100, next at level 200).

    Local Notation "action ;; next" :=
      (bind action (fun _ => next))
      (at level 100, right associativity).

    Definition solve_owner
        (bottom : D)
        (operations : owner_operations V D Monad)
        (constraint_system : system Monad)
        (owner : V) : Monad unit :=
      begin_evaluation operations owner ;;
      let* direct :=
        match constraint_system owner with
        | Some body =>
            eval_transfer
              (read_value operations owner)
              (emit_side_effect operations owner)
              (spawn_variable operations owner)
              body
        | None => ret bottom
        end in
      commit_value operations owner direct ;;
      drain_owner operations owner.

    Fixpoint solve_worklist
        (fuel : nat)
        (pop_owner : unit -> Monad (option V))
        (solve_queued_owner : V -> Monad unit) : Monad solve_result :=
      match fuel with
      | 0 => ret OutOfFuel
      | S remaining =>
          let* picked := pop_owner tt in
          match picked with
          | None => ret Solved
          | Some owner =>
              solve_queued_owner owner ;;
              solve_worklist remaining pop_owner solve_queued_owner
          end
      end.

    Definition solve_with_fuel
        (fuel : nat)
        (initialize_roots : list V -> Monad unit)
        (pop_owner : unit -> Monad (option V))
        (solve_queued_owner : V -> Monad unit)
        (roots : list V) : Monad solve_result :=
      initialize_roots roots ;;
      solve_worklist fuel pop_owner solve_queued_owner.

    Fixpoint drain_with_fuel
        (fuel : nat)
        (pop_owner : unit -> Monad (option V))
        (solve_queued_owner : V -> Monad unit) : Monad seeded_result :=
      let* picked := pop_owner tt in
      match picked with
      | None => ret (SeedsSolved fuel)
      | Some owner =>
          match fuel with
          | 0 => ret SeedsOutOfFuel
          | S remaining =>
              solve_queued_owner owner ;;
              drain_with_fuel remaining pop_owner solve_queued_owner
          end
      end.

    (** Discover roots one at a time. An unstarted root is solved directly,
        and all work it creates is drained before the next root is observed.
        A direct root evaluation consumes one unit of the common fuel. *)
    Fixpoint solve_seeds_with_fuel
        (fuel : nat)
        (is_started : V -> Monad bool)
        (pop_owner : unit -> Monad (option V))
        (solve_owner : V -> Monad unit)
        (roots : list V) : Monad seeded_result :=
      match roots with
      | [] => ret (SeedsSolved fuel)
      | root :: remaining_roots =>
          let* started := is_started root in
          if started
          then
            solve_seeds_with_fuel fuel is_started pop_owner solve_owner
              remaining_roots
          else
            match fuel with
            | 0 => ret SeedsOutOfFuel
            | S remaining_fuel =>
                solve_owner root ;;
                let* drained :=
                  drain_with_fuel remaining_fuel pop_owner solve_owner in
                match drained with
                | SeedsOutOfFuel => ret SeedsOutOfFuel
                | SeedsSolved after_drain =>
                    solve_seeds_with_fuel after_drain is_started pop_owner
                      solve_owner remaining_roots
                end
            end
      end.
  End Solver.
