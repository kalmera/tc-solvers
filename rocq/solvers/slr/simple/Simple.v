From Stdlib Require Import List Bool.
From TcSolvers Require Export
  common.Interfaces
  common.ConstraintSystems
  solvers.slr.common.Monadic
  solvers.slr.common.DiscoveryOrder.
From TcSolvers Require Import common.Collections.

Import ListNotations.
Set Implicit Arguments.

(** Public monadic presentation. The control flow is shared, while this
    variant supplies persistent-phase state operations to the callbacks. *)
Module Monadic := Monadic.

(** Stable partial-rank version of the persistent-phase solver.

    The ranking policy is explicit.  Correctness will require only stable,
    injective ranks: it will not require fresh ranks to be greatest or dense.

    There are no restarting episodes.  Ordinary and side-effect phases live
    in maps for the lifetime of the solver.  [local_sides] is the only
    addition to the tagged algorithm: it accumulates repeated emissions to
    one target during a single RHS evaluation. *)

Module Make
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Rk : DISCOVERY_ORDER V).

  Module ConstraintSystem := ConstraintSystems.Make V D.
  Import ConstraintSystem.

  Definition store := M.t D.t.
  Definition readers_table := M.t S.t.
  Definition contribution_row := M.t D.t.
  Definition contribution_table := M.t contribution_row.
  Definition phase_table := M.t U.phase.
  Definition side_phase_row := M.t U.phase.
  Definition side_phase_table := M.t side_phase_row.
  Definition local_side_row := M.t D.t.
  Definition local_side_table := M.t local_side_row.

  Module Ranking := Rk.

  Record handle := {
    handle_variable : V.t;
    handle_rank : nat;
  }.

  Definition work_queue := list handle.

  Fixpoint queue_contains_rank (rank : nat) (q : work_queue) : bool :=
    match q with
    | [] => false
    | head :: rest =>
        if PeanoNat.Nat.eq_dec rank (handle_rank head)
        then true
        else queue_contains_rank rank rest
    end.

  Fixpoint queue_insert_fresh (entry : handle) (q : work_queue) : work_queue :=
    match q with
    | [] => [entry]
    | head :: rest =>
        if Nat.ltb (handle_rank head) (handle_rank entry)
        then entry :: head :: rest
        else head :: queue_insert_fresh entry rest
    end.

  Definition queue_insert (entry : handle) (q : work_queue) : work_queue :=
    if queue_contains_rank (handle_rank entry) q
    then q
    else queue_insert_fresh entry q.

  Definition queue_peek (q : work_queue) : option handle :=
    match q with
    | [] => None
    | head :: _ => Some head
    end.

  Definition queue_pop (q : work_queue) : option (handle * work_queue) :=
    match q with
    | [] => None
    | head :: rest => Some (head, rest)
    end.

  Record state := {
    sigma : store;
    ranking : Ranking.t;
    queue : work_queue;
    started : S.t;
    readers : readers_table;
    contributions : contribution_table;
    phases : phase_table;
    side_phases : side_phase_table;
    local_sides : local_side_table;
    controlled : S.t;
  }.

  Definition with_sigma (st : state) (next : store) : state :=
    {| sigma := next;
       ranking := ranking st;
       queue := queue st;
       started := started st;
       readers := readers st;
       contributions := contributions st;
       phases := phases st;
       side_phases := side_phases st;
       local_sides := local_sides st;
       controlled := controlled st |}.

  Definition with_ranking (st : state) (next : Ranking.t) : state :=
    {| sigma := sigma st;
       ranking := next;
       queue := queue st;
       started := started st;
       readers := readers st;
       contributions := contributions st;
       phases := phases st;
       side_phases := side_phases st;
       local_sides := local_sides st;
       controlled := controlled st |}.

  Definition with_queue (st : state) (next : work_queue) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := next;
       started := started st;
       readers := readers st;
       contributions := contributions st;
       phases := phases st;
       side_phases := side_phases st;
       local_sides := local_sides st;
       controlled := controlled st |}.

  Definition with_started (st : state) (next : S.t) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       started := next;
       readers := readers st;
       contributions := contributions st;
       phases := phases st;
       side_phases := side_phases st;
       local_sides := local_sides st;
       controlled := controlled st |}.

  Definition with_readers (st : state) (next : readers_table) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       started := started st;
       readers := next;
       contributions := contributions st;
       phases := phases st;
       side_phases := side_phases st;
       local_sides := local_sides st;
       controlled := controlled st |}.

  Definition with_contributions
    (st : state) (next : contribution_table) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       started := started st;
       readers := readers st;
       contributions := next;
       phases := phases st;
       side_phases := side_phases st;
       local_sides := local_sides st;
       controlled := controlled st |}.

  Definition with_phases (st : state) (next : phase_table) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       started := started st;
       readers := readers st;
       contributions := contributions st;
       phases := next;
       side_phases := side_phases st;
       local_sides := local_sides st;
       controlled := controlled st |}.

  Definition with_side_phases
    (st : state) (next : side_phase_table) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       started := started st;
       readers := readers st;
       contributions := contributions st;
       phases := phases st;
       side_phases := next;
       local_sides := local_sides st;
       controlled := controlled st |}.

  Definition with_local_sides
    (st : state) (next : local_side_table) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       started := started st;
       readers := readers st;
       contributions := contributions st;
       phases := phases st;
       side_phases := side_phases st;
       local_sides := next;
       controlled := controlled st |}.

  Definition with_controlled (st : state) (next : S.t) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       started := started st;
       readers := readers st;
       contributions := contributions st;
       phases := phases st;
       side_phases := side_phases st;
       local_sides := local_sides st;
       controlled := next |}.

  Definition empty_state : state :=
    {| sigma := M.empty D.t;
       ranking := Ranking.empty;
       queue := [];
       started := S.empty;
       readers := M.empty S.t;
       contributions := M.empty contribution_row;
       phases := M.empty U.phase;
       side_phases := M.empty side_phase_row;
       local_sides := M.empty local_side_row;
       controlled := S.empty |}.

  Definition lookup_map {A : Type}
    (table : M.t (M.t A)) (outer : V.t) : M.t A :=
    match M.lookup table outer with
    | Some row => row
    | None => M.empty A
    end.

  Definition update_map {A : Type}
    (table : M.t (M.t A)) (outer inner : V.t) (value : A) :
    M.t (M.t A) :=
    M.update table outer
      (M.update (lookup_map table outer) inner value).

  Definition lookup_set (table : M.t S.t) (x : V.t) : S.t :=
    match M.lookup table x with
    | Some xs => xs
    | None => S.empty
    end.

  Definition sigma_value (st : state) (x : V.t) : D.t :=
    match M.lookup (sigma st) x with
    | Some value => value
    | None => D.bottom
    end.

  Definition is_materialized (st : state) (x : V.t) : bool :=
    match M.lookup (sigma st) x with
    | Some _ => true
    | None => false
    end.

  Definition materialize (st : state) (x : V.t) : state :=
    if is_materialized st x
    then st
    else with_sigma st (M.update (sigma st) x D.bottom).

  Definition observe (st : state) (x : V.t) : state * handle :=
    let '(next_ranking, rank) := Ranking.observe (ranking st) x in
    (with_ranking st next_ranking,
      {| handle_variable := x; handle_rank := rank |}).

  Definition enqueue_handle (st : state) (entry : handle) : state :=
    with_queue st (queue_insert entry (queue st)).

  Definition enqueue (st : state) (x : V.t) : state :=
    let '(st1, entry) := observe st x in
    enqueue_handle st1 entry.

  Fixpoint enqueue_all (st : state) (xs : list V.t) : state :=
    match xs with
    | [] => st
    | x :: rest => enqueue_all (enqueue st x) rest
    end.

  Definition equivalent (left right : D.t) : bool :=
    andb (D.leq left right) (D.leq right left).

  Fixpoint join_values (values : list D.t) : D.t :=
    match values with
    | [] => D.bottom
    | value :: rest => D.join value (join_values rest)
    end.

  Definition aggregate (st : state) (target : V.t) : D.t :=
    join_values (M.values (lookup_map (contributions st) target)).

  Definition stored_contribution
    (st : state) (source target : V.t) : D.t :=
    match M.lookup (lookup_map (contributions st) target) source with
    | Some value => value
    | None => D.bottom
    end.

  Definition stored_phase (st : state) (owner : V.t) : U.phase :=
    match M.lookup (phases st) owner with
    | Some phase => phase
    | None => U.initial_phase false owner
    end.

  Definition stored_side_phase
    (st : state) (source target : V.t) : U.phase :=
    match M.lookup (lookup_map (side_phases st) target) source with
    | Some phase => phase
    | None => U.initial_phase true target
    end.

  Definition promote_controlled (st : state) (x : V.t) : state :=
    with_controlled st (S.add x (controlled st)).

  Definition add_reader
    (st : state) (target owner : V.t) : state :=
    with_readers st
      (M.update (readers st) target
        (S.add owner (lookup_set (readers st) target))).

  Definition get_ready_state
    (st : state) (owner target : handle) : state :=
    let st1 :=
      if Nat.ltb (handle_rank owner) (handle_rank target)
      then st
      else promote_controlled st (handle_variable target) in
    materialize
      (add_reader st1 (handle_variable target) (handle_variable owner))
      (handle_variable target).

  Definition reset_local_sides (st : state) (owner : V.t) : state :=
    with_local_sides st
      (M.update (local_sides st) owner (M.empty D.t)).

  Definition start_evaluation (st : state) (owner : V.t) : state :=
    reset_local_sides (materialize st owner) owner.

  Definition accumulated_side_input
    (st : state) (source target : V.t) (raw : D.t) : D.t :=
    match M.lookup (lookup_map (local_sides st) source) target with
    | Some previous => D.join previous raw
    | None => raw
    end.

  Definition record_side_payload
    (st : state) (source target : V.t) (raw : D.t) : state :=
    let input := accumulated_side_input st source target raw in
    let phase := stored_side_phase st source target in
    let old := stored_contribution st source target in
    let updated := U.update true target phase old input in
    let st1 := with_local_sides st
      (update_map (local_sides st) source target input) in
    let st2 := with_contributions st1
      (update_map (contributions st1) target source (snd updated)) in
    with_side_phases st2
      (update_map (side_phases st2) target source (fst updated)).

  Definition side_ready_state
    (st : state) (source target : handle) (raw : D.t) : state :=
    let st1 := record_side_payload st
      (handle_variable source) (handle_variable target) raw in
    if Nat.ltb (handle_rank target) (handle_rank source)
    then st1
    else promote_controlled st1 (handle_variable source).

  Definition write_changed_value
    (st : state) (owner : V.t) (value : D.t) : state :=
    let invalidated := S.elements (lookup_set (readers st) owner) in
    let st1 := with_sigma st (M.update (sigma st) owner value) in
    let st2 := enqueue_all st1 invalidated in
    with_readers st2 (M.update (readers st2) owner S.empty).

  Definition set_value
    (st : state) (owner : V.t) (direct : D.t) : state :=
    let candidate := D.join direct (aggregate st owner) in
    let old := sigma_value st owner in
    if equivalent candidate old then st
    else if S.mem owner (controlled st) then
      let updated :=
        U.update false owner (stored_phase st owner) old candidate in
      let st1 :=
        with_phases st (M.update (phases st) owner (fst updated)) in
      if equivalent (snd updated) old
      then st1
      else write_changed_value st1 owner (snd updated)
    else write_changed_value st owner candidate.

  Definition owner_may_still_be_queued
    (st : state) (owner : handle) : bool :=
    match queue_peek (queue st) with
    | None => false
    | Some head =>
        if V.eq_dec (handle_variable head) (handle_variable owner)
        then true
        else Nat.ltb (handle_rank owner) (handle_rank head)
    end.

  Inductive control : Type :=
  | RunLoop
  | RunSeeds : list V.t -> control
  | RunSeedLoop : list V.t -> control
  | RunSolveOne : handle -> continuation -> control
  | RunSolveOneLoop : handle -> continuation -> control
  | RunRhs : handle -> rhs -> continuation -> control
  | AfterGet : handle -> handle -> (D.t -> rhs) -> continuation -> control
  | AfterSide : handle -> rhs -> continuation -> control
  | AfterSpawn : handle -> rhs -> continuation -> control
  with continuation : Type :=
  | KLoop
  | KSeedLoop : list V.t -> continuation
  | KSolveOneLoop : handle -> continuation -> continuation
  | KAfterGet :
      handle -> handle -> (D.t -> rhs) -> continuation -> continuation
  | KAfterSide : handle -> rhs -> continuation -> continuation
  | KAfterSpawn : handle -> rhs -> continuation -> continuation.

  Definition continue (k : continuation) : control :=
    match k with
    | KLoop => RunLoop
    | KSeedLoop remaining => RunSeedLoop remaining
    | KSolveOneLoop owner rest => RunSolveOneLoop owner rest
    | KAfterGet owner target next rest =>
        AfterGet owner target next rest
    | KAfterSide owner next rest => AfterSide owner next rest
    | KAfterSpawn owner next rest => AfterSpawn owner next rest
    end.

  Record config := {
    cfg_state : state;
    cfg_control : control;
  }.

  Definition initial_config (initial : list V.t) : config :=
    {| cfg_state := empty_state;
       cfg_control := RunSeeds initial |}.

  Definition next_config (tf : system) (c : config) : option config :=
    let st := cfg_state c in
    match cfg_control c with
    | RunLoop =>
        match queue_pop (queue st) with
        | Some (owner, rest) =>
            Some
              {| cfg_state := with_queue st rest;
                 cfg_control := RunSolveOne owner KLoop |}
        | None => None
        end

    | RunSeeds roots =>
        match roots with
        | [] => Some {| cfg_state := st; cfg_control := RunLoop |}
        | root :: remaining =>
            let '(st1, owner) := observe st root in
            if S.mem root (started st1)
            then
              Some {| cfg_state := st1; cfg_control := RunSeeds remaining |}
            else
              Some
                {| cfg_state := st1;
                   cfg_control := RunSolveOne owner (KSeedLoop remaining) |}
        end

    | RunSeedLoop remaining =>
        match queue_pop (queue st) with
        | Some (owner, rest) =>
            Some
              {| cfg_state := with_queue st rest;
                 cfg_control := RunSolveOne owner (KSeedLoop remaining) |}
        | None =>
            Some {| cfg_state := st; cfg_control := RunSeeds remaining |}
        end

    | RunSolveOne owner k =>
        let variable := handle_variable owner in
        let st1 := start_evaluation st variable in
        Some
          {| cfg_state := with_started st1 (S.add variable (started st1));
             cfg_control := RunRhs owner (tf variable) k |}

    | RunSolveOneLoop owner k =>
        if owner_may_still_be_queued st owner then
          match queue_pop (queue st) with
          | Some (next, rest) =>
              if V.eq_dec (handle_variable next) (handle_variable owner) then
                Some
                  {| cfg_state := with_queue st rest;
                     cfg_control := RunSolveOne owner k |}
              else
                Some
                  {| cfg_state := with_queue st rest;
                     cfg_control :=
                       RunSolveOne next (KSolveOneLoop owner k) |}
          | None => None
          end
        else if D.leq
          (aggregate st (handle_variable owner))
          (sigma_value st (handle_variable owner))
        then Some {| cfg_state := st; cfg_control := continue k |}
        else None

    | RunRhs owner body k =>
        let owner_variable := handle_variable owner in
        match body with
        | Ret direct =>
            Some
              {| cfg_state := set_value st owner_variable direct;
                 cfg_control := RunSolveOneLoop owner k |}

        | Get target next =>
            let '(st0, target_handle) := observe st target in
            if is_materialized st0 target then
              let st1 := get_ready_state st0 owner target_handle in
              Some
                {| cfg_state := st1;
                   cfg_control :=
                     RunRhs owner (next (sigma_value st1 target)) k |}
            else if Nat.ltb (handle_rank owner) (handle_rank target_handle) then
              Some
                {| cfg_state := st0;
                   cfg_control :=
                     RunSolveOne target_handle
                       (KAfterGet owner target_handle next k) |}
            else
              let st1 := get_ready_state
                (enqueue_handle st0 target_handle) owner target_handle in
              Some
                {| cfg_state := st1;
                   cfg_control :=
                     RunRhs owner (next (sigma_value st1 target)) k |}

        | Side target raw next =>
            let '(st0, target_handle) := observe st target in
            let st1 := side_ready_state st0 owner target_handle raw in
            let changed :=
              negb (D.leq
                (aggregate st1 target) (aggregate st0 target)) in
            if changed then
              if andb
                  (Nat.ltb (handle_rank owner) (handle_rank target_handle))
                  (negb (is_materialized st0 target))
              then
                Some
                  {| cfg_state := st1;
                     cfg_control :=
                       RunSolveOne target_handle (KAfterSide owner next k) |}
              else
                Some
                  {| cfg_state := enqueue_handle st1 target_handle;
                     cfg_control := RunRhs owner next k |}
            else
              Some
                {| cfg_state := st1;
                   cfg_control := RunRhs owner next k |}

        | Spawn target next =>
            let '(st0, target_handle) := observe st target in
            if is_materialized st0 target then
              Some
                {| cfg_state := st0;
                   cfg_control := RunRhs owner next k |}
            else if Nat.ltb (handle_rank owner) (handle_rank target_handle) then
              Some
                {| cfg_state := st0;
                   cfg_control :=
                     RunSolveOne target_handle (KAfterSpawn owner next k) |}
            else
              Some
                {| cfg_state := materialize
                    (enqueue_handle st0 target_handle) target;
                   cfg_control := RunRhs owner next k |}
        end

    | AfterGet owner target next k =>
        let target_variable := handle_variable target in
        if is_materialized st target_variable then
          let st1 := get_ready_state st owner target in
          Some
            {| cfg_state := st1;
               cfg_control :=
                 RunRhs owner (next (sigma_value st1 target_variable)) k |}
        else None

    | AfterSide owner next k =>
        Some
          {| cfg_state := st;
             cfg_control := RunRhs owner next k |}

    | AfterSpawn owner next k =>
        Some
          {| cfg_state := st;
             cfg_control := RunRhs owner next k |}
    end.

  Fixpoint run_fuel
    (fuel : nat) (tf : system) (c : config) : config :=
    match fuel with
    | 0 => c
    | S rest =>
        match next_config tf c with
        | Some next => run_fuel rest tf next
        | None => c
        end
    end.

  Definition terminal_state (c : config) : option state :=
    match cfg_control c with
    | RunLoop =>
        match queue_peek (queue (cfg_state c)) with
        | None => Some (cfg_state c)
        | Some _ => None
        end
    | _ => None
    end.

  Definition solve_fuel
    (fuel : nat) (tf : system) (initial : list V.t) : option state :=
    terminal_state (run_fuel fuel tf (initial_config initial)).

  Definition solve_values_fuel
    (fuel : nat) (tf : system) (initial : list V.t) : option store :=
    match solve_fuel fuel tf initial with
    | Some final => Some (sigma final)
    | None => None
    end.

End Make.

Module FirstDiscoveryAlgorithm
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D).

  Module S := ListSet V.
  Module M := AssocMap V.
  Module Rk := ListDiscoveryOrder V.
  Include Make V D U S M Rk.
End FirstDiscoveryAlgorithm.

(** First-discovery policy with caller-supplied collections.  This is the
    extraction-facing form of the online instance. *)
Module FirstDiscovery
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V).

  Module Rk := ListDiscoveryOrder V.
  Include Make V D U S M Rk.
End FirstDiscovery.

Module FixedRank
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Fixed : STATELESS_RANK V).

  Module Rk := FixedRankDiscoveryOrder V Fixed.
  Include Make V D U S M Rk.
End FixedRank.
