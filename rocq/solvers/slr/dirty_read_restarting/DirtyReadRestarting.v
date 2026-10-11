From Stdlib Require Import List Bool.
From TcSolvers Require Export
  common.Interfaces
  common.ConstraintSystems
  solvers.slr.common.Monadic
  solvers.slr.common.DiscoveryOrder.
From TcSolvers Require Import
  common.Collections
  common.SideUpdate
  solvers.slr.common.FirstActivation.

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

(** Pure, executable small-step .

    This is the primary formal artifact.  It contains no proof instrumentation
    and is intended to be extracted directly. *)

Module Core
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (SU : SIDE_UPDATE V D)
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

  Fixpoint queue_remove (x : V.t) (q : work_queue) : work_queue :=
    match q with
    | [] => []
    | head :: rest =>
        if V.eq_dec x head then rest else head :: queue_remove x rest
    end.

  Record side_cell := {
    side_phase : SU.phase;
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
    dormant_bottom : S.t;
    controlled : S.t;
    dirty_side_targets : M.t bool;
    deferred_wakes : work_queue;
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
       dormant_bottom := S.empty;
       controlled := S.empty;
       dirty_side_targets := M.empty bool;
       deferred_wakes := [] |}.

  Definition with_sigma (st : state) (next : store) : state :=
    {| sigma := next;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       dormant_bottom := dormant_bottom st;
       controlled := controlled st;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := deferred_wakes st |}.

  Definition with_ranking (st : state) (next : Ranking.t) : state :=
    {| sigma := sigma st;
       ranking := next;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       dormant_bottom := dormant_bottom st;
       controlled := controlled st;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := deferred_wakes st |}.

  Definition with_queue (st : state) (next : work_queue) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := next;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       dormant_bottom := dormant_bottom st;
       controlled := controlled st;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := deferred_wakes st |}.

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
       dormant_bottom := dormant_bottom st;
       controlled := controlled st;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := deferred_wakes st |}.

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
       dormant_bottom := dormant_bottom st;
       controlled := controlled st;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := deferred_wakes st |}.

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
       dormant_bottom := dormant_bottom st;
       controlled := controlled st;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := deferred_wakes st |}.

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
       dormant_bottom := dormant_bottom st;
       controlled := controlled st;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := deferred_wakes st |}.

  Definition with_dormant_bottom (st : state) (next : S.t) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       dormant_bottom := next;
       controlled := controlled st;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := deferred_wakes st |}.

  Definition with_controlled (st : state) (next : S.t) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       dormant_bottom := dormant_bottom st;
       controlled := next;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := deferred_wakes st |}.

  Definition with_dirty_side_targets
    (st : state) (next : M.t bool) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       dormant_bottom := dormant_bottom st;
       controlled := controlled st;
       dirty_side_targets := next;
       deferred_wakes := deferred_wakes st |}.

  Definition with_deferred_wakes
    (st : state) (next : work_queue) : state :=
    {| sigma := sigma st;
       ranking := ranking st;
       queue := queue st;
       readers := readers st;
       contributions := contributions st;
       side_cells := side_cells st;
       reset_at_close := reset_at_close st;
       last_targets := last_targets st;
       dormant_bottom := dormant_bottom st;
       controlled := controlled st;
       dirty_side_targets := dirty_side_targets st;
       deferred_wakes := next |}.

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

  Definition is_dormant (st : state) (x : V.t) : bool :=
    andb (S.mem x (dormant_bottom st))
      (andb
        (match M.lookup (sigma st) x with
         | Some _ => false
         | None => true
         end)
        (match Ranking.lookup (ranking st) x with
         | Some _ => false
         | None => true
         end)).

  Definition remember_dormant (st : state) (x : V.t) : state :=
    with_dormant_bottom st (S.add x (dormant_bottom st)).

  Definition semantic_lookup (st : state) (x : V.t) : option D.t :=
    match M.lookup (sigma st) x with
    | Some value => Some value
    | None => if S.mem x (dormant_bottom st) then Some D.bottom else None
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

  Definition add_reader (st : state) (target owner : V.t) : state :=
    with_readers st
      (M.update (readers st) target
        (S.add owner (lookup_set (readers st) target))).

  Definition rank_lt (st : state) (x y : V.t) : bool :=
    ranking_lt (ranking st) x y.

  Definition enqueue (st : state) (x : V.t) : state :=
    with_queue st (queue_insert (ranking st) x (queue st)).

  Definition enqueue_all (st : state) (xs : list V.t) : state :=
    with_queue st (queue_insert_all (ranking st) xs (queue st)).

  Definition defer_all (st : state) (xs : list V.t) : state :=
    with_deferred_wakes st
      (queue_insert_all (ranking st) xs (deferred_wakes st)).

  Definition flush_deferred (st : state) : state :=
    with_deferred_wakes (enqueue_all st (deferred_wakes st)) [].

  Definition mark_side_dirty (st : state) (target : V.t) : state :=
    with_dirty_side_targets st
      (M.update (dirty_side_targets st) target true).

  Definition clear_side_dirty (st : state) (target : V.t) : state :=
    with_dirty_side_targets st
      (M.update (dirty_side_targets st) target false).

  Definition is_side_dirty (st : state) (target : V.t) : bool :=
    match M.lookup (dirty_side_targets st) target with
    | Some dirty => dirty
    | None => false
    end.

  Definition cancel_dirty_target (st : state) (target : V.t) : state :=
    clear_side_dirty
      (with_queue st (queue_remove target (queue st))) target.

  Definition equivalent (left right : D.t) : bool :=
    andb (D.leq left right) (D.leq right left).

  Fixpoint join_values (values : list D.t) : D.t :=
    match values with
    | [] => D.bottom
    | value :: rest => D.join value (join_values rest)
    end.

  Definition aggregate (st : state) (target : V.t) : D.t :=
    join_values (M.values (lookup_map (contributions st) target)).

  Definition aggregate_changed
    (before after : state) (target : V.t) : bool :=
    negb (equivalent (aggregate after target) (aggregate before target)).

  Definition aggregate_grew
    (before after : state) (target : V.t) : bool :=
    negb (D.leq (aggregate after target) (aggregate before target)).

  Definition stored_contribution
    (st : state) (source target : V.t) : D.t :=
    match M.lookup (lookup_map (contributions st) target) source with
    | Some value => value
    | None => D.bottom
    end.

  Definition default_side_cell (source target : V.t) : side_cell :=
    {| side_phase := SU.initial_phase source target;
       side_reset_at := None |}.

  Definition stored_side_cell
    (st : state) (source target : V.t) : side_cell :=
    match M.lookup (lookup_map (side_cells st) source) target with
    | Some cell => cell
    | None => default_side_cell source target
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
    (st : state) (source target scope : V.t) (phase : SU.phase) : state :=
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
        let fresh := default_side_cell source target in
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

  Definition write_dirty_value
    (st : state) (target : V.t) (value : D.t) : state :=
    let st1 := with_sigma st (M.update (sigma st) target value) in
    let invalidated := S.elements (lookup_set (readers st1) target) in
    let st2 := defer_all st1 invalidated in
    with_readers st2 (M.update (readers st2) target S.empty).

  (** Complete pending work for an exact RHS-less target at a non-self read.
      Restarting deliberately discards the phase selected by this shortened
      fresh episode. A decreasing result remains queued for normal control. *)
  Definition try_dirty_read
    (tf : system) (st : state) (owner target : V.t) : option state :=
    if V.eq_dec owner target then None
    else if is_side_dirty st target then
      match tf target with
      | Ret direct =>
          if equivalent direct D.bottom then
            let candidate := D.join direct (aggregate st target) in
            let old := sigma_value st target in
            let was_controlled := S.mem target (controlled st) in
            let st0 := promote_controlled st target in
            if equivalent candidate old then
              Some (cancel_dirty_target st0 target)
            else if was_controlled then
              let updated := U.update false target
                (U.initial_phase false target) old candidate in
              if D.leq old (snd updated) then
                let st1 := cancel_dirty_target st0 target in
                if equivalent (snd updated) old
                then Some st1
                else Some (write_dirty_value st1 target (snd updated))
              else None
            else if D.leq old candidate then
              Some (write_dirty_value
                (cancel_dirty_target st0 target) target candidate)
            else None
          else None
      | _ => None
      end
    else None.

  Definition dirty_complete_get
    (tf : system) (st : state) (fr : frame) (target : V.t) :
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
    let prepared := materialize st1 target in
    let flushed :=
      match try_dirty_read tf prepared owner target with
      | Some next => next
      | None => prepared
      end in
    let st2 := add_reader flushed target owner in
    (st2, fr1, sigma_value st2 target).

  Definition publish_dormant_target
    (st : state) (target : V.t) (changed : bool) : state :=
    let value := aggregate st target in
    let st1 := materialize st target in
    if changed then
      let invalidated := S.elements (lookup_set (readers st1) target) in
      let st2 := with_sigma st1 (M.update (sigma st1) target value) in
      let st3 := enqueue_all st2 invalidated in
      with_readers st3 (M.update (readers st3) target S.empty)
    else st1.

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

  Definition side_update
    (st : state) (source target : V.t) (input : D.t) : SU.phase * D.t :=
    let cell := stored_side_cell st source target in
    let old_target_aggregate := aggregate st target in
    SU.update source target (side_phase cell)
      (stored_contribution st source target) input old_target_aggregate.

  Definition write_side_contribution
    (st : state) (fr : frame) (target : V.t) (input : D.t) :
    state * bool :=
    let source := frame_owner fr in
    let st1 := promote_side_target st fr target in
    let updated := side_update st1 source target input in
    let next_phase := fst updated in
    let next_contribution := snd updated in
    let st2 := with_contributions st1
      (update_map (contributions st1) target source next_contribution) in
    let st3 := register_reset st2 source target
      (frame_min_scope fr) next_phase in
    let changed := aggregate_changed st1 st3 target in
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

  Definition pure_bottom_rhs (tf : system) (variable : V.t) : bool :=
    match tf variable with
    | Ret direct => equivalent direct D.bottom
    | _ => false
    end.

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
            if orb (is_materialized st root) (is_dormant st root)
            then
              Some {| cfg_state := st; cfg_control := RunSeeds remaining |}
            else match Ranking.lookup (ranking st) root with
              | None =>
                  if pure_bottom_rhs tf root then
                    Some
                      {| cfg_state := remember_dormant st root;
                         cfg_control := RunSeeds remaining |}
                  else
                    let st1 := observe st root in
                    Some
                      {| cfg_state := st1;
                         cfg_control :=
                           StartEpisode root (KSeedLoop remaining) |}
              | Some _ =>
                  let st1 := observe st root in
                  Some
                    {| cfg_state := st1;
                       cfg_control :=
                         StartEpisode root (KSeedLoop remaining) |}
              end
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
        let st1 := clear_side_dirty (materialize st owner) owner in
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
            if is_dormant st target then
              Some
                {| cfg_state := add_reader st target (frame_owner fr);
                   cfg_control := RunRhs fr (kget D.bottom) k |}
            else match Ranking.lookup (ranking st) target with
              | None =>
                  if andb (pure_bottom_rhs tf target)
                      (negb (is_materialized st target)) then
                    let st1 := remember_dormant st target in
                    Some
                      {| cfg_state :=
                           add_reader st1 target (frame_owner fr);
                         cfg_control := RunRhs fr (kget D.bottom) k |}
                  else
                    let st0 := observe st target in
                    if andb (negb (is_materialized st0 target))
                        (rank_lt st0 (frame_owner fr) target)
                    then
                      Some
                        {| cfg_state := st0;
                           cfg_control :=
                             StartEpisode target
                               (KAfterGet fr target kget k) |}
                    else
                      let st1 :=
                        if is_materialized st0 target
                        then st0 else enqueue st0 target in
                      let '(st2, fr1, value) :=
                        complete_get st1 fr target in
                      Some
                        {| cfg_state := st2;
                           cfg_control := RunRhs fr1 (kget value) k |}
              | Some _ =>
                  let st0 := observe st target in
                  if is_materialized st0 target then
                    let '(st1, fr1, value) :=
                      dirty_complete_get tf st0 fr target in
                    Some
                      {| cfg_state := st1;
                         cfg_control := RunRhs fr1 (kget value) k |}
                  else if rank_lt st0 (frame_owner fr) target then
                    Some
                      {| cfg_state := st0;
                         cfg_control :=
                           StartEpisode target
                             (KAfterGet fr target kget k) |}
                  else
                    let st1 := enqueue st0 target in
                    let '(st2, fr1, value) :=
                      complete_get st1 fr target in
                    Some
                      {| cfg_state := st2;
                         cfg_control := RunRhs fr1 (kget value) k |}
              end

        | Side target raw next =>
            let was_dormant := is_dormant st target in
            let st0 := observe st target in
            let '(fr1, input) := record_side_input fr target raw in
            let '(st1, changed) :=
              write_side_contribution st0 fr1 target input in
            if was_dormant then
              Some (continue_side st1 fr1 target next k true)
            else if changed then
              Some (continue_side (mark_side_dirty st1 target)
                fr1 target next k true)
            else
              Some (continue_side st1 fr1 target next k false)

        | Spawn target next =>
            if is_dormant st target then
              Some
                {| cfg_state := st;
                   cfg_control := RunRhs fr next k |}
            else match Ranking.lookup (ranking st) target with
              | None =>
                  if andb (pure_bottom_rhs tf target)
                      (negb (is_materialized st target)) then
                    Some
                      {| cfg_state := remember_dormant st target;
                         cfg_control := RunRhs fr next k |}
                  else
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
                        {| cfg_state :=
                             materialize (enqueue st0 target) target;
                           cfg_control := RunRhs fr next k |}
              | Some _ =>
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
                      {| cfg_state :=
                           materialize (enqueue st0 target) target;
                         cfg_control := RunRhs fr next k |}
              end
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
              let st2 := if changed then mark_side_dirty st1 target else st1 in
              Some (continue_dead st2 fr direct target remaining k changed)
        end

    | RunCommit fr direct k =>
        let '(st1, fr1) := set_value (flush_deferred st) fr direct in
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
                  let st1 := clear_side_dirty (with_queue st rest)
                    (frame_owner fr) in
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
        match queue_peek (queue (cfg_state c)),
              queue_peek (deferred_wakes (cfg_state c)) with
        | None, None => Some (cfg_state c)
        | _, _ => None
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

End Core.

(** Public second-paper algorithm. Ranking is dense and append-only at first
    activation; dormant demands receive no rank until promotion. *)
Module Make
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (SU : SIDE_UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Features : FEATURES).

  Module Rk := ListDiscoveryOrder V.
  Include Core V D U SU S M Rk Features.
End Make.

Module FirstDiscoveryAlgorithm
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (SU : SIDE_UPDATE V D).

  Module S := ListSet V.
  Module M := AssocMap V.
  Include Make V D U SU S M AllEnabledFeatures.
End FirstDiscoveryAlgorithm.

Module FirstDiscovery
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (SU : SIDE_UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Features : FEATURES).

  Include Make V D U SU S M Features.
End FirstDiscovery.
