From Stdlib Require Import List Bool.
From TcSolvers Require Export
  common.Interfaces
  common.ConstraintSystems
  solvers.slr.common.Monadic
  solvers.slr.common.DiscoveryOrder.
From TcSolvers Require Import common.Collections.

Import ListNotations.
Set Implicit Arguments.

(** Normal phases always restart at a new owner episode. These two constants
    select the remaining restarting policies. *)
Module Type FEATURES.
  Parameter restart_side_phases : bool.
  Parameter eliminate_dead_sides : bool.
End FEATURES.

Module AllEnabledFeatures <: FEATURES.
  Definition restart_side_phases := true.
  Definition eliminate_dead_sides := true.
End AllEnabledFeatures.

(** Public monadic presentation. The control flow is shared, while this
    variant supplies eager restarting operations to the callbacks. *)
Module Monadic := Monadic.

(** Pure, executable small-step SLRTC.

    This is the primary formal artifact.  It contains no proof instrumentation
    and is intended to be extracted directly. *)

Module Make
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (Features : FEATURES).

  Module ConstraintSystem := ConstraintSystems.Make V D.
  Import ConstraintSystem.

  Definition store := M.t D.t.
  Definition readers_table := M.t S.t.
  Definition contribution_row := M.t D.t.
  Definition contribution_table := M.t contribution_row.
  Module Ranking := Rk.

  Definition work_queue := list V.t.

  Definition ranking_lt (order : Ranking.t) (x y : V.t) : bool :=
    match Ranking.lookup order x, Ranking.lookup order y with
    | Some x_rank, Some y_rank => Nat.ltb x_rank y_rank
    | _, _ => false
    end.

  Fixpoint queue_contains (x : V.t) (q : work_queue) : bool :=
    match q with
    | [] => false
    | head :: rest =>
        if V.eq_dec x head then true else queue_contains x rest
    end.

  Fixpoint queue_insert_fresh
    (order : Ranking.t) (x : V.t) (q : work_queue) : work_queue :=
    match q with
    | [] => [x]
    | head :: rest =>
        if ranking_lt order head x
        then x :: head :: rest
        else head :: queue_insert_fresh order x rest
    end.

  Definition queue_insert
    (order : Ranking.t) (x : V.t) (q : work_queue) : work_queue :=
    if queue_contains x q then q else queue_insert_fresh order x q.

  Fixpoint queue_insert_all
    (order : Ranking.t) (xs : list V.t) (q : work_queue) : work_queue :=
    match xs with
    | [] => q
    | x :: rest => queue_insert_all order rest (queue_insert order x q)
    end.

  Definition queue_peek (q : work_queue) : option V.t :=
    match q with
    | [] => None
    | head :: _ => Some head
    end.

  Definition queue_pop (q : work_queue) : option (V.t * work_queue) :=
    match q with
    | [] => None
    | head :: rest => Some (head, rest)
    end.

  Record side_cell := {
    side_phase : U.phase;
    side_reset_at : option V.t;
  }.

  Definition side_cell_row := M.t side_cell.
  Definition side_cell_table := M.t side_cell_row.
  Definition side_cell_id := (V.t * V.t)%type.
  Definition reset_table := M.t (list side_cell_id).
  Definition target_table := M.t S.t.

  Record state := {
    sigma : store;
    ranking : Ranking.t;
    queue : work_queue;
    readers : readers_table;
    contributions : contribution_table;
    side_cells : side_cell_table;
    reset_at_close : reset_table;
    last_targets : target_table;
    controlled : S.t;
  }.

  Definition empty_state : state :=
    {| sigma := M.empty D.t;
       ranking := Ranking.empty;
       queue := [];
       readers := M.empty S.t;
       contributions := M.empty contribution_row;
       side_cells := M.empty side_cell_row;
       reset_at_close := M.empty (list side_cell_id);
       last_targets := M.empty S.t;
       controlled := S.empty |}.

  Definition with_sigma (st : state) (next : store) : state :=
    {| sigma := next;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       controlled := controlled st |}.

  Definition with_ranking (st : state) (next : Ranking.t) : state :=
    {| sigma := sigma st;
       ranking := next;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       controlled := controlled st |}.

  Definition with_queue (st : state) (next : work_queue) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := next;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       controlled := controlled st |}.

  Definition with_readers
    (st : state) (next : readers_table) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       readers := next;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       controlled := controlled st |}.

  Definition with_contributions
    (st : state) (next : contribution_table) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := next;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       controlled := controlled st |}.

  Definition with_cells_and_resets
    (st : state) (cells : side_cell_table) (resets : reset_table) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := cells;
       reset_at_close := resets;
       last_targets := last_targets st;
       controlled := controlled st |}.

  Definition with_last_targets
    (st : state) (next : target_table) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := next;
       controlled := controlled st |}.

  Definition with_controlled (st : state) (next : S.t) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       controlled := next |}.

  Definition lookup_map {A : Type}
    (table : M.t (M.t A)) (outer : V.t) : M.t A :=
    match M.lookup table outer with
    | Some row => row
    | None => M.empty A
    end.

  Definition update_map {A : Type}
    (table : M.t (M.t A)) (outer inner : V.t) (value : A) :
    M.t (M.t A) :=
    let row := lookup_map table outer in
    M.update table outer (M.update row inner value).

  Definition lookup_set (table : M.t S.t) (x : V.t) : S.t :=
    match M.lookup table x with
    | Some xs => xs
    | None => S.empty
    end.

  Definition lookup_reset_ids
    (table : reset_table) (scope : V.t) : list side_cell_id :=
    match M.lookup table scope with
    | Some ids => ids
    | None => []
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
    match M.lookup (sigma st) x with
    | Some _ => st
    | None => with_sigma st (M.update (sigma st) x D.bottom)
    end.

  Definition observe (st : state) (x : V.t) : state :=
    let '(next, _) := Ranking.observe (ranking st) x in
    with_ranking st next.

  Definition rank_lt (st : state) (x y : V.t) : bool :=
    ranking_lt (ranking st) x y.

  Definition enqueue (st : state) (x : V.t) : state :=
    with_queue st (queue_insert (ranking st) x (queue st)).

  Definition enqueue_all (st : state) (xs : list V.t) : state :=
    with_queue st (queue_insert_all (ranking st) xs (queue st)).

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

  Definition default_side_cell (target : V.t) : side_cell :=
    {| side_phase := U.initial_phase true target;
       side_reset_at := None |}.

  Definition stored_side_cell
    (st : state) (source target : V.t) : side_cell :=
    match M.lookup (lookup_map (side_cells st) source) target with
    | Some cell => cell
    | None => default_side_cell target
    end.

  Definition cell_id_eq_dec :
    forall left right : side_cell_id, {left = right} + {left <> right}.
  Proof.
    decide equality; apply V.eq_dec.
  Defined.

  Fixpoint remove_cell_id
    (id : side_cell_id) (ids : list side_cell_id) : list side_cell_id :=
    match ids with
    | [] => []
    | candidate :: rest =>
        if cell_id_eq_dec id candidate
        then remove_cell_id id rest
        else candidate :: remove_cell_id id rest
    end.

  Definition add_cell_id
    (id : side_cell_id) (ids : list side_cell_id) : list side_cell_id :=
    if List.in_dec cell_id_eq_dec id ids then ids else id :: ids.

  Definition remove_registration
    (resets : reset_table) (scope : V.t) (id : side_cell_id) :
    reset_table :=
    M.update resets scope
      (remove_cell_id id (lookup_reset_ids resets scope)).

  Definition add_registration
    (resets : reset_table) (scope : V.t) (id : side_cell_id) :
    reset_table :=
    M.update resets scope
      (add_cell_id id (lookup_reset_ids resets scope)).

  Definition same_scope (left right : option V.t) : bool :=
    match left, right with
    | Some x, Some y => if V.eq_dec x y then true else false
    | None, None => true
    | _, _ => false
    end.

  Definition register_reset
    (st : state) (source target scope : V.t) (phase : U.phase) : state :=
    let id := (source, target) in
    let old_cell := stored_side_cell st source target in
    let eligible := rank_lt st scope target in
    let requested :=
      if Features.restart_side_phases
      then if eligible then Some scope else None
      else None in
    let same := same_scope (side_reset_at old_cell) requested in
    let without_old :=
      if same then reset_at_close st
      else
        match side_reset_at old_cell with
        | Some previous =>
            remove_registration (reset_at_close st) previous id
        | None => reset_at_close st
        end in
    let next_resets :=
      if same then without_old
      else
        match requested with
        | Some next => add_registration without_old next id
        | None => without_old
        end in
    let next_cell :=
      {| side_phase := phase;
         side_reset_at := requested |} in
    with_cells_and_resets st
      (update_map (side_cells st) source target next_cell)
      next_resets.

  Fixpoint reset_cells
    (ids : list side_cell_id) (cells : side_cell_table) :
    side_cell_table :=
    match ids with
    | [] => cells
    | (source, target) :: rest =>
        let fresh := default_side_cell target in
        reset_cells rest (update_map cells source target fresh)
    end.

  Definition reset_registered_cells
    (st : state) (owner : V.t) : state :=
    if Features.restart_side_phases then
      let ids := lookup_reset_ids (reset_at_close st) owner in
      with_cells_and_resets st
        (reset_cells ids (side_cells st))
        (M.update (reset_at_close st) owner [])
    else st.

  Record frame := {
    frame_owner : V.t;
    frame_phase : U.phase;
    frame_local_side : M.t D.t;
    frame_previous_targets : S.t;
    frame_current_targets : S.t;
    frame_min_scope : V.t;
    frame_max_read : option V.t;
  }.

  Definition fresh_frame
    (st : state) (owner : V.t) (phase : U.phase) : frame :=
    {| frame_owner := owner;
       frame_phase := phase;
       frame_local_side := M.empty D.t;
       frame_previous_targets := lookup_set (last_targets st) owner;
       frame_current_targets := S.empty;
       frame_min_scope := owner;
       frame_max_read := None |}.

  Definition with_frame_phase (fr : frame) (phase : U.phase) : frame :=
    {| frame_owner := frame_owner fr;
       frame_phase := phase;
       frame_local_side := frame_local_side fr;
       frame_previous_targets := frame_previous_targets fr;
       frame_current_targets := frame_current_targets fr;
       frame_min_scope := frame_min_scope fr;
       frame_max_read := frame_max_read fr |}.

  Definition with_frame_read
    (fr : frame) (minimum : V.t) (maximum : option V.t) : frame :=
    {| frame_owner := frame_owner fr;
       frame_phase := frame_phase fr;
       frame_local_side := frame_local_side fr;
       frame_previous_targets := frame_previous_targets fr;
       frame_current_targets := frame_current_targets fr;
       frame_min_scope := minimum;
       frame_max_read := maximum |}.

  Definition with_frame_side
    (fr : frame) (target : V.t) (input : D.t) : frame :=
    {| frame_owner := frame_owner fr;
       frame_phase := frame_phase fr;
       frame_local_side :=
         M.update (frame_local_side fr) target input;
       frame_previous_targets := frame_previous_targets fr;
       frame_current_targets :=
         S.add target (frame_current_targets fr);
       frame_min_scope := frame_min_scope fr;
       frame_max_read := frame_max_read fr |}.

  Definition promote_controlled
    (st : state) (x : V.t) : state :=
    with_controlled st (S.add x (controlled st)).

  Definition complete_get
    (st : state) (fr : frame) (target : V.t) :
    state * frame * D.t :=
    let owner := frame_owner fr in
    let st1 :=
      if rank_lt st owner target then st else promote_controlled st target in
    let minimum :=
      if rank_lt st target (frame_min_scope fr)
      then target
      else frame_min_scope fr in
    let maximum :=
      match frame_max_read fr with
      | None => Some target
      | Some previous =>
          if rank_lt st previous target then Some target else Some previous
      end in
    let fr1 := with_frame_read fr minimum maximum in
    let current_readers := lookup_set (readers st1) target in
    let st2 := with_readers st1
      (M.update (readers st1) target (S.add owner current_readers)) in
    let st3 := materialize st2 target in
    (st3, fr1, sigma_value st3 target).

  Definition accumulated_side_input
    (fr : frame) (target : V.t) (raw : D.t) : D.t :=
    match M.lookup (frame_local_side fr) target with
    | Some previous => D.join previous raw
    | None => raw
    end.

  Definition record_side_input
    (fr : frame) (target : V.t) (raw : D.t) : frame * D.t :=
    let input := accumulated_side_input fr target raw in
    (with_frame_side fr target input, input).

  Definition promote_side_target
    (st : state) (fr : frame) (target : V.t) : state :=
    let source := frame_owner fr in
    if rank_lt st target source then st else promote_controlled st source.

  Definition write_side_contribution
    (st : state) (fr : frame) (target : V.t) (input : D.t) :
    state * bool :=
    let source := frame_owner fr in
    let st1 := promote_side_target st fr target in
    let old_aggregate := aggregate st1 target in
    let old_contribution := stored_contribution st1 source target in
    let cell := stored_side_cell st1 source target in
    let updated :=
      U.update true target (side_phase cell) old_contribution input in
    let next_phase := fst updated in
    let next_contribution := snd updated in
    let st2 := with_contributions st1
      (update_map (contributions st1) target source next_contribution) in
    let st3 := register_reset st2 source target
      (frame_min_scope fr) next_phase in
    let changed := negb (equivalent (aggregate st3 target) old_aggregate) in
    (st3, changed).

  Definition publish_targets (st : state) (fr : frame) : state :=
    with_last_targets st
      (M.update (last_targets st)
        (frame_owner fr) (frame_current_targets fr)).

  Definition set_value
    (st : state) (fr : frame) (direct : D.t) : state * frame :=
    let owner := frame_owner fr in
    let candidate := D.join direct (aggregate st owner) in
    let old := sigma_value st owner in
    if equivalent candidate old then (st, fr)
    else
      let result :=
        if S.mem owner (controlled st)
        then U.update false owner (frame_phase fr) old candidate
        else (frame_phase fr, candidate) in
      let next_phase := fst result in
      let value := snd result in
      let fr1 := with_frame_phase fr next_phase in
      if equivalent value old then (st, fr1)
      else
        let st1 := with_sigma st (M.update (sigma st) owner value) in
        let invalidated := S.elements (lookup_set (readers st1) owner) in
        let st2 := enqueue_all st1 invalidated in
        let st3 := with_readers st2
          (M.update (readers st2) owner S.empty) in
        (st3, fr1).


  Inductive control : Type :=
  | RunLoop
  | RunSeeds : list V.t -> control
  | RunSeedLoop : list V.t -> control
  | StartEpisode : V.t -> continuation -> control
  | RunRhs : frame -> rhs -> continuation -> control
  | RunDead : frame -> D.t -> list V.t -> continuation -> control
  | RunCommit : frame -> D.t -> continuation -> control
  | RunDrain : frame -> continuation -> control
  | Return : continuation -> control
  with continuation : Type :=
  | KLoop
  | KSeedLoop : list V.t -> continuation
  | KAfterGet : frame -> V.t -> (D.t -> rhs) -> continuation -> continuation
  | KAfterSide : frame -> rhs -> continuation -> continuation
  | KAfterSpawn : frame -> rhs -> continuation -> continuation
  | KDead : frame -> D.t -> list V.t -> continuation -> continuation
  | KDrain : frame -> continuation -> continuation.

  Record config := {
    cfg_state : state;
    cfg_control : control;
  }.

  Definition initial_config (initial : list V.t) : config :=
    {| cfg_state := empty_state;
       cfg_control := RunSeeds initial |}.

  Definition continue_side
    (st : state) (fr : frame) (target : V.t)
    (next : rhs) (k : continuation) (changed : bool) : config :=
    if changed then
      if andb (rank_lt st (frame_owner fr) target)
          (negb (is_materialized st target))
      then
        {| cfg_state := st;
           cfg_control :=
             StartEpisode target (KAfterSide fr next k) |}
      else
        {| cfg_state := enqueue st target;
           cfg_control := RunRhs fr next k |}
    else
      {| cfg_state := st;
         cfg_control := RunRhs fr next k |}.

  Definition continue_dead
    (st : state) (fr : frame) (direct : D.t)
    (target : V.t) (remaining : list V.t)
    (k : continuation) (changed : bool) : config :=
    if changed then
      if andb (rank_lt st (frame_owner fr) target)
          (negb (is_materialized st target))
      then
        {| cfg_state := st;
           cfg_control :=
             StartEpisode target (KDead fr direct remaining k) |}
      else
        {| cfg_state := enqueue st target;
           cfg_control := RunDead fr direct remaining k |}
    else
      {| cfg_state := st;
         cfg_control := RunDead fr direct remaining k |}.

  Definition next_config (tf : system) (c : config) : option config :=
    let st := cfg_state c in
    match cfg_control c with
    | RunLoop =>
        match queue_pop (queue st) with
        | None => None
        | Some (owner, rest) =>
            Some
              {| cfg_state := with_queue st rest;
                 cfg_control := StartEpisode owner KLoop |}
        end

    | RunSeeds roots =>
        match roots with
        | [] => Some {| cfg_state := st; cfg_control := RunLoop |}
        | root :: remaining =>
            let st1 := observe st root in
            if is_materialized st1 root
            then
              Some {| cfg_state := st1; cfg_control := RunSeeds remaining |}
            else
              Some
                {| cfg_state := st1;
                   cfg_control := StartEpisode root (KSeedLoop remaining) |}
        end

    | RunSeedLoop remaining =>
        match queue_pop (queue st) with
        | Some (owner, rest) =>
            Some
              {| cfg_state := with_queue st rest;
                 cfg_control := StartEpisode owner (KSeedLoop remaining) |}
        | None =>
            Some {| cfg_state := st; cfg_control := RunSeeds remaining |}
        end

    | StartEpisode owner k =>
        let st1 := materialize st owner in
        let phase := U.initial_phase false owner in
        Some
          {| cfg_state := st1;
             cfg_control := RunRhs (fresh_frame st1 owner phase) (tf owner) k |}

    | RunRhs fr body k =>
        match body with
        | Ret direct =>
            Some
              {| cfg_state := st;
                 cfg_control :=
                   RunDead fr direct
                     (if Features.eliminate_dead_sides
                      then S.elements (frame_previous_targets fr)
                      else []) k |}

        | Get target kget =>
            let st0 := observe st target in
            if andb (negb (is_materialized st0 target))
                (rank_lt st0 (frame_owner fr) target)
            then
              Some
                {| cfg_state := st0;
                   cfg_control :=
                     StartEpisode target (KAfterGet fr target kget k) |}
            else
              let st1 :=
                if is_materialized st0 target then st0 else enqueue st0 target in
              let '(st2, fr1, value) := complete_get st1 fr target in
              Some
                {| cfg_state := st2;
                   cfg_control := RunRhs fr1 (kget value) k |}

        | Side target raw next =>
            let st0 := observe st target in
            let '(fr1, input) := record_side_input fr target raw in
            let '(st1, changed) :=
              write_side_contribution st0 fr1 target input in
            Some (continue_side st1 fr1 target next k changed)

        | Spawn target next =>
            let st0 := observe st target in
            if is_materialized st0 target then
              Some
                {| cfg_state := st0;
                   cfg_control := RunRhs fr next k |}
            else if rank_lt st0 (frame_owner fr) target then
              Some
                {| cfg_state := st0;
                   cfg_control :=
                     StartEpisode target (KAfterSpawn fr next k) |}
            else
              Some
                {| cfg_state := materialize (enqueue st0 target) target;
                   cfg_control := RunRhs fr next k |}
        end

    | RunDead fr direct pending k =>
        match pending with
        | [] =>
            Some
              {| cfg_state := publish_targets st fr;
                 cfg_control := RunCommit fr direct k |}
        | target :: remaining =>
            if S.mem target (frame_current_targets fr) then
              Some
                {| cfg_state := st;
                   cfg_control := RunDead fr direct remaining k |}
            else
              let '(st1, changed) :=
                write_side_contribution st fr target D.bottom in
              Some (continue_dead st1 fr direct target remaining k changed)
        end

    | RunCommit fr direct k =>
        let '(st1, fr1) := set_value st fr direct in
        Some
          {| cfg_state := st1;
             cfg_control := RunDrain fr1 k |}

    | RunDrain fr k =>
        match queue_peek (queue st) with
        | None =>
            Some
              {| cfg_state :=
                   reset_registered_cells st (frame_owner fr);
                 cfg_control := Return k |}
        | Some next =>
            if V.eq_dec next (frame_owner fr) then
              match queue_pop (queue st) with
              | Some (_, rest) =>
                  let st1 := with_queue st rest in
                  Some
                    {| cfg_state := st1;
                       cfg_control :=
                         RunRhs
                           (fresh_frame st1
                             (frame_owner fr) (frame_phase fr))
                           (tf (frame_owner fr)) k |}
              | None => None
              end
            else if rank_lt st (frame_owner fr) next then
              match queue_pop (queue st) with
              | Some (_, rest) =>
                  Some
                    {| cfg_state := with_queue st rest;
                       cfg_control := StartEpisode next (KDrain fr k) |}
              | None => None
              end
            else
              Some
                {| cfg_state :=
                     reset_registered_cells st (frame_owner fr);
                   cfg_control := Return k |}
        end

    | Return k =>
        match k with
        | KLoop =>
            Some {| cfg_state := st; cfg_control := RunLoop |}

        | KSeedLoop remaining =>
            Some {| cfg_state := st; cfg_control := RunSeedLoop remaining |}

        | KAfterGet fr target kget k' =>
            let '(st1, fr1, value) := complete_get st fr target in
            Some
              {| cfg_state := st1;
                 cfg_control := RunRhs fr1 (kget value) k' |}

        | KAfterSide fr next k' =>
            Some
              {| cfg_state := st;
                 cfg_control := RunRhs fr next k' |}

        | KAfterSpawn fr next k' =>
            Some
              {| cfg_state := st;
                 cfg_control := RunRhs fr next k' |}

        | KDead fr direct remaining k' =>
            Some
              {| cfg_state := st;
                 cfg_control := RunDead fr direct remaining k' |}

        | KDrain fr k' =>
            Some
              {| cfg_state := st;
                 cfg_control := RunDrain fr k' |}
        end
    end.

  Fixpoint run_fuel (fuel : nat) (tf : system) (c : config) : config :=
    match fuel with
    | O => c
    | S remaining =>
        match next_config tf c with
        | Some next => run_fuel remaining tf next
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

End Make.
