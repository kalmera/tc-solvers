open Collections
open ConstraintSystems
open Datatypes
open DiscoveryOrder
open Interfaces
open Monadic
open Nat

type __ = Obj.t

module Monadic :
 sig
  type ('v, 'd, 'monad) transfer =
    ('v -> 'monad) -> ('v -> 'd -> 'monad) -> ('v -> 'monad) -> 'monad

  type ('v, 'd, 'monad) system = 'v -> ('v, 'd, 'monad) transfer option

  val eval_transfer :
    ('a1 -> 'a3) -> ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1, 'a2, 'a3)
    transfer -> 'a3

  type ('v, 'd, 'monad) owner_operations = ('v, 'd, 'monad) Monadic.owner_operations = { 
  begin_evaluation : ('v -> 'monad); read_value : ('v -> 'v -> 'monad);
  emit_side_effect : ('v -> 'v -> 'd -> 'monad);
  spawn_variable : ('v -> 'v -> 'monad); commit_value : ('v -> 'd -> 'monad);
  drain_owner : ('v -> 'monad) }

  val begin_evaluation : ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a3

  val read_value : ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a1 -> 'a3

  val emit_side_effect :
    ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a1 -> 'a2 -> 'a3

  val spawn_variable : ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a1 -> 'a3

  val commit_value : ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a2 -> 'a3

  val drain_owner : ('a1, 'a2, 'a3) owner_operations -> 'a1 -> 'a3

  type solve_result = Monadic.solve_result =
  | Solved
  | OutOfFuel

  val solve_result_rect : 'a1 -> 'a1 -> solve_result -> 'a1

  val solve_result_rec : 'a1 -> 'a1 -> solve_result -> 'a1

  type seeded_result = Monadic.seeded_result =
  | SeedsSolved of int
  | SeedsOutOfFuel

  val seeded_result_rect : (int -> 'a1) -> 'a1 -> seeded_result -> 'a1

  val seeded_result_rec : (int -> 'a1) -> 'a1 -> seeded_result -> 'a1

  val solve_owner :
    (__ -> __ -> 'a3) -> (__ -> __ -> 'a3 -> (__ -> 'a3) -> 'a3) -> 'a2 ->
    ('a1, 'a2, 'a3) owner_operations -> ('a1, 'a2, 'a3) system -> 'a1 -> 'a3

  val solve_worklist :
    (__ -> __ -> 'a2) -> (__ -> __ -> 'a2 -> (__ -> 'a2) -> 'a2) -> int ->
    (unit -> 'a2) -> ('a1 -> 'a2) -> 'a2

  val solve_with_fuel :
    (__ -> __ -> 'a2) -> (__ -> __ -> 'a2 -> (__ -> 'a2) -> 'a2) -> int ->
    ('a1 list -> 'a2) -> (unit -> 'a2) -> ('a1 -> 'a2) -> 'a1 list -> 'a2

  val drain_with_fuel :
    (__ -> __ -> 'a2) -> (__ -> __ -> 'a2 -> (__ -> 'a2) -> 'a2) -> int ->
    (unit -> 'a2) -> ('a1 -> 'a2) -> 'a2

  val solve_seeds_with_fuel :
    (__ -> __ -> 'a2) -> (__ -> __ -> 'a2 -> (__ -> 'a2) -> 'a2) -> int ->
    ('a1 -> 'a2) -> (unit -> 'a2) -> ('a1 -> 'a2) -> 'a1 list -> 'a2
 end

module Make :
 functor (V:VAR) ->
 functor (D:DOMAIN) ->
 functor (U:sig
  type phase

  val initial_phase : bool -> V.t -> phase

  val update : bool -> V.t -> phase -> D.t -> D.t -> phase * D.t
 end) ->
 functor (S:sig
  type t

  val empty : t

  val mem : V.t -> t -> bool

  val add : V.t -> t -> t

  val elements : t -> V.t list
 end) ->
 functor (M:sig
  type 'x t

  val empty : 'a1 t

  val lookup : 'a1 t -> V.t -> 'a1 option

  val update : 'a1 t -> V.t -> 'a1 -> 'a1 t

  val values : 'a1 t -> 'a1 list
 end) ->
 functor (Rk:sig
  type t

  val empty : t

  val lookup : t -> V.t -> int option

  val size : t -> int

  val observe : t -> V.t -> t * int
 end) ->
 sig
  module ConstraintSystem :
   sig
    type rhs =
    | Ret of D.t
    | Get of V.t * (D.t -> rhs)
    | Side of V.t * D.t * rhs
    | Spawn of V.t * rhs

    val rhs_rect :
      (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
      D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

    val rhs_rec :
      (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
      D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

    type system = V.t -> rhs
   end

  type store = D.t M.t

  type readers_table = S.t M.t

  type contribution_row = D.t M.t

  type contribution_table = contribution_row M.t

  type phase_table = U.phase M.t

  type side_phase_row = U.phase M.t

  type side_phase_table = side_phase_row M.t

  type local_side_row = D.t M.t

  type local_side_table = local_side_row M.t

  module Ranking :
   sig
    type t = Rk.t

    val empty : t

    val lookup : t -> V.t -> int option

    val size : t -> int

    val observe : t -> V.t -> t * int
   end

  type handle = { handle_variable : V.t; handle_rank : int }

  val handle_variable : handle -> V.t

  val handle_rank : handle -> int

  type work_queue = handle list

  val queue_contains_rank : int -> work_queue -> bool

  val queue_insert_fresh : handle -> work_queue -> work_queue

  val queue_insert : handle -> work_queue -> work_queue

  val queue_peek : work_queue -> handle option

  val queue_pop : work_queue -> (handle * work_queue) option

  type state = { sigma : store; ranking : Ranking.t; queue : work_queue;
                 started : S.t; readers : readers_table;
                 contributions : contribution_table; phases : phase_table;
                 side_phases : side_phase_table;
                 local_sides : local_side_table; controlled : S.t }

  val sigma : state -> store

  val ranking : state -> Ranking.t

  val queue : state -> work_queue

  val started : state -> S.t

  val readers : state -> readers_table

  val contributions : state -> contribution_table

  val phases : state -> phase_table

  val side_phases : state -> side_phase_table

  val local_sides : state -> local_side_table

  val controlled : state -> S.t

  val with_sigma : state -> store -> state

  val with_ranking : state -> Ranking.t -> state

  val with_queue : state -> work_queue -> state

  val with_started : state -> S.t -> state

  val with_readers : state -> readers_table -> state

  val with_contributions : state -> contribution_table -> state

  val with_phases : state -> phase_table -> state

  val with_side_phases : state -> side_phase_table -> state

  val with_local_sides : state -> local_side_table -> state

  val with_controlled : state -> S.t -> state

  val empty_state : state

  val lookup_map : 'a1 M.t M.t -> V.t -> 'a1 M.t

  val update_map : 'a1 M.t M.t -> V.t -> V.t -> 'a1 -> 'a1 M.t M.t

  val lookup_set : S.t M.t -> V.t -> S.t

  val sigma_value : state -> V.t -> D.t

  val is_materialized : state -> V.t -> bool

  val materialize : state -> V.t -> state

  val observe : state -> V.t -> state * handle

  val enqueue_handle : state -> handle -> state

  val enqueue : state -> V.t -> state

  val enqueue_all : state -> V.t list -> state

  val equivalent : D.t -> D.t -> bool

  val join_values : D.t list -> D.t

  val aggregate : state -> V.t -> D.t

  val stored_contribution : state -> V.t -> V.t -> D.t

  val stored_phase : state -> V.t -> U.phase

  val stored_side_phase : state -> V.t -> V.t -> U.phase

  val promote_controlled : state -> V.t -> state

  val add_reader : state -> V.t -> V.t -> state

  val get_ready_state : state -> handle -> handle -> state

  val reset_local_sides : state -> V.t -> state

  val start_evaluation : state -> V.t -> state

  val accumulated_side_input : state -> V.t -> V.t -> D.t -> D.t

  val record_side_payload : state -> V.t -> V.t -> D.t -> state

  val side_ready_state : state -> handle -> handle -> D.t -> state

  val write_changed_value : state -> V.t -> D.t -> state

  val set_value : state -> V.t -> D.t -> state

  val owner_may_still_be_queued : state -> handle -> bool

  type control =
  | RunLoop
  | RunSeeds of V.t list
  | RunSeedLoop of V.t list
  | RunSolveOne of handle * continuation
  | RunSolveOneLoop of handle * continuation
  | RunRhs of handle * ConstraintSystem.rhs * continuation
  | AfterGet of handle * handle * (D.t -> ConstraintSystem.rhs) * continuation
  | AfterSide of handle * ConstraintSystem.rhs * continuation
  | AfterSpawn of handle * ConstraintSystem.rhs * continuation
  and continuation =
  | KLoop
  | KSeedLoop of V.t list
  | KSolveOneLoop of handle * continuation
  | KAfterGet of handle * handle * (D.t -> ConstraintSystem.rhs)
     * continuation
  | KAfterSide of handle * ConstraintSystem.rhs * continuation
  | KAfterSpawn of handle * ConstraintSystem.rhs * continuation

  val control_rect :
    'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (handle -> continuation
    -> 'a1) -> (handle -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle -> handle -> (D.t
    -> ConstraintSystem.rhs) -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> control -> 'a1

  val control_rec :
    'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (handle -> continuation
    -> 'a1) -> (handle -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle -> handle -> (D.t
    -> ConstraintSystem.rhs) -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> control -> 'a1

  val continuation_rect :
    'a1 -> (V.t list -> 'a1) -> (handle -> continuation -> 'a1 -> 'a1) ->
    (handle -> handle -> (D.t -> ConstraintSystem.rhs) -> continuation -> 'a1
    -> 'a1) -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1)
    -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) ->
    continuation -> 'a1

  val continuation_rec :
    'a1 -> (V.t list -> 'a1) -> (handle -> continuation -> 'a1 -> 'a1) ->
    (handle -> handle -> (D.t -> ConstraintSystem.rhs) -> continuation -> 'a1
    -> 'a1) -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1)
    -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) ->
    continuation -> 'a1

  val continue : continuation -> control

  type config = { cfg_state : state; cfg_control : control }

  val cfg_state : config -> state

  val cfg_control : config -> control

  val initial_config : V.t list -> config

  val next_config : ConstraintSystem.system -> config -> config option

  val run_fuel : int -> ConstraintSystem.system -> config -> config

  val terminal_state : config -> state option

  val solve_fuel : int -> ConstraintSystem.system -> V.t list -> state option

  val solve_values_fuel :
    int -> ConstraintSystem.system -> V.t list -> store option
 end

module FirstDiscoveryAlgorithm :
 functor (V:VAR) ->
 functor (D:DOMAIN) ->
 functor (U:sig
  type phase

  val initial_phase : bool -> V.t -> phase

  val update : bool -> V.t -> phase -> D.t -> D.t -> phase * D.t
 end) ->
 sig
  module S :
   sig
    type t = V.t list

    val empty : t

    val mem : V.t -> t -> bool

    val add : V.t -> t -> t

    val elements : t -> V.t list
   end

  module M :
   sig
    type 'a t = (V.t * 'a) list

    val empty : 'a1 t

    val lookup : 'a1 t -> V.t -> 'a1 option

    val update : 'a1 t -> V.t -> 'a1 -> 'a1 t

    val values : 'a1 t -> 'a1 list
   end

  module Rk :
   sig
    type t = V.t list

    val empty : t

    val lookup : t -> V.t -> int option

    val size : t -> int

    val observe : t -> V.t -> t * int
   end

  module ConstraintSystem :
   sig
    type rhs =
    | Ret of D.t
    | Get of V.t * (D.t -> rhs)
    | Side of V.t * D.t * rhs
    | Spawn of V.t * rhs

    val rhs_rect :
      (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
      D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

    val rhs_rec :
      (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
      D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

    type system = V.t -> rhs
   end

  type store = D.t M.t

  type readers_table = S.t M.t

  type contribution_row = D.t M.t

  type contribution_table = contribution_row M.t

  type phase_table = U.phase M.t

  type side_phase_row = U.phase M.t

  type side_phase_table = side_phase_row M.t

  type local_side_row = D.t M.t

  type local_side_table = local_side_row M.t

  module Ranking :
   sig
    type t = Rk.t

    val empty : t

    val lookup : t -> V.t -> int option

    val size : t -> int

    val observe : t -> V.t -> t * int
   end

  type handle = { handle_variable : V.t; handle_rank : int }

  val handle_variable : handle -> V.t

  val handle_rank : handle -> int

  type work_queue = handle list

  val queue_contains_rank : int -> work_queue -> bool

  val queue_insert_fresh : handle -> work_queue -> work_queue

  val queue_insert : handle -> work_queue -> work_queue

  val queue_peek : work_queue -> handle option

  val queue_pop : work_queue -> (handle * work_queue) option

  type state = { sigma : store; ranking : Ranking.t; queue : work_queue;
                 started : S.t; readers : readers_table;
                 contributions : contribution_table; phases : phase_table;
                 side_phases : side_phase_table;
                 local_sides : local_side_table; controlled : S.t }

  val sigma : state -> store

  val ranking : state -> Ranking.t

  val queue : state -> work_queue

  val started : state -> S.t

  val readers : state -> readers_table

  val contributions : state -> contribution_table

  val phases : state -> phase_table

  val side_phases : state -> side_phase_table

  val local_sides : state -> local_side_table

  val controlled : state -> S.t

  val with_sigma : state -> store -> state

  val with_ranking : state -> Ranking.t -> state

  val with_queue : state -> work_queue -> state

  val with_started : state -> S.t -> state

  val with_readers : state -> readers_table -> state

  val with_contributions : state -> contribution_table -> state

  val with_phases : state -> phase_table -> state

  val with_side_phases : state -> side_phase_table -> state

  val with_local_sides : state -> local_side_table -> state

  val with_controlled : state -> S.t -> state

  val empty_state : state

  val lookup_map : 'a1 M.t M.t -> V.t -> 'a1 M.t

  val update_map : 'a1 M.t M.t -> V.t -> V.t -> 'a1 -> 'a1 M.t M.t

  val lookup_set : S.t M.t -> V.t -> S.t

  val sigma_value : state -> V.t -> D.t

  val is_materialized : state -> V.t -> bool

  val materialize : state -> V.t -> state

  val observe : state -> V.t -> state * handle

  val enqueue_handle : state -> handle -> state

  val enqueue : state -> V.t -> state

  val enqueue_all : state -> V.t list -> state

  val equivalent : D.t -> D.t -> bool

  val join_values : D.t list -> D.t

  val aggregate : state -> V.t -> D.t

  val stored_contribution : state -> V.t -> V.t -> D.t

  val stored_phase : state -> V.t -> U.phase

  val stored_side_phase : state -> V.t -> V.t -> U.phase

  val promote_controlled : state -> V.t -> state

  val add_reader : state -> V.t -> V.t -> state

  val get_ready_state : state -> handle -> handle -> state

  val reset_local_sides : state -> V.t -> state

  val start_evaluation : state -> V.t -> state

  val accumulated_side_input : state -> V.t -> V.t -> D.t -> D.t

  val record_side_payload : state -> V.t -> V.t -> D.t -> state

  val side_ready_state : state -> handle -> handle -> D.t -> state

  val write_changed_value : state -> V.t -> D.t -> state

  val set_value : state -> V.t -> D.t -> state

  val owner_may_still_be_queued : state -> handle -> bool

  type control =
  | RunLoop
  | RunSeeds of V.t list
  | RunSeedLoop of V.t list
  | RunSolveOne of handle * continuation
  | RunSolveOneLoop of handle * continuation
  | RunRhs of handle * ConstraintSystem.rhs * continuation
  | AfterGet of handle * handle * (D.t -> ConstraintSystem.rhs) * continuation
  | AfterSide of handle * ConstraintSystem.rhs * continuation
  | AfterSpawn of handle * ConstraintSystem.rhs * continuation
  and continuation =
  | KLoop
  | KSeedLoop of V.t list
  | KSolveOneLoop of handle * continuation
  | KAfterGet of handle * handle * (D.t -> ConstraintSystem.rhs)
     * continuation
  | KAfterSide of handle * ConstraintSystem.rhs * continuation
  | KAfterSpawn of handle * ConstraintSystem.rhs * continuation

  val control_rect :
    'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (handle -> continuation
    -> 'a1) -> (handle -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle -> handle -> (D.t
    -> ConstraintSystem.rhs) -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> control -> 'a1

  val control_rec :
    'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (handle -> continuation
    -> 'a1) -> (handle -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle -> handle -> (D.t
    -> ConstraintSystem.rhs) -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> control -> 'a1

  val continuation_rect :
    'a1 -> (V.t list -> 'a1) -> (handle -> continuation -> 'a1 -> 'a1) ->
    (handle -> handle -> (D.t -> ConstraintSystem.rhs) -> continuation -> 'a1
    -> 'a1) -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1)
    -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) ->
    continuation -> 'a1

  val continuation_rec :
    'a1 -> (V.t list -> 'a1) -> (handle -> continuation -> 'a1 -> 'a1) ->
    (handle -> handle -> (D.t -> ConstraintSystem.rhs) -> continuation -> 'a1
    -> 'a1) -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1)
    -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) ->
    continuation -> 'a1

  val continue : continuation -> control

  type config = { cfg_state : state; cfg_control : control }

  val cfg_state : config -> state

  val cfg_control : config -> control

  val initial_config : V.t list -> config

  val next_config : ConstraintSystem.system -> config -> config option

  val run_fuel : int -> ConstraintSystem.system -> config -> config

  val terminal_state : config -> state option

  val solve_fuel : int -> ConstraintSystem.system -> V.t list -> state option

  val solve_values_fuel :
    int -> ConstraintSystem.system -> V.t list -> store option
 end

module FirstDiscovery :
 functor (V:VAR) ->
 functor (D:DOMAIN) ->
 functor (U:sig
  type phase

  val initial_phase : bool -> V.t -> phase

  val update : bool -> V.t -> phase -> D.t -> D.t -> phase * D.t
 end) ->
 functor (S:sig
  type t

  val empty : t

  val mem : V.t -> t -> bool

  val add : V.t -> t -> t

  val elements : t -> V.t list
 end) ->
 functor (M:sig
  type 'x t

  val empty : 'a1 t

  val lookup : 'a1 t -> V.t -> 'a1 option

  val update : 'a1 t -> V.t -> 'a1 -> 'a1 t

  val values : 'a1 t -> 'a1 list
 end) ->
 sig
  module Rk :
   sig
    type t = V.t list

    val empty : t

    val lookup : t -> V.t -> int option

    val size : t -> int

    val observe : t -> V.t -> t * int
   end

  module ConstraintSystem :
   sig
    type rhs =
    | Ret of D.t
    | Get of V.t * (D.t -> rhs)
    | Side of V.t * D.t * rhs
    | Spawn of V.t * rhs

    val rhs_rect :
      (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
      D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

    val rhs_rec :
      (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
      D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

    type system = V.t -> rhs
   end

  type store = D.t M.t

  type readers_table = S.t M.t

  type contribution_row = D.t M.t

  type contribution_table = contribution_row M.t

  type phase_table = U.phase M.t

  type side_phase_row = U.phase M.t

  type side_phase_table = side_phase_row M.t

  type local_side_row = D.t M.t

  type local_side_table = local_side_row M.t

  module Ranking :
   sig
    type t = Rk.t

    val empty : t

    val lookup : t -> V.t -> int option

    val size : t -> int

    val observe : t -> V.t -> t * int
   end

  type handle = { handle_variable : V.t; handle_rank : int }

  val handle_variable : handle -> V.t

  val handle_rank : handle -> int

  type work_queue = handle list

  val queue_contains_rank : int -> work_queue -> bool

  val queue_insert_fresh : handle -> work_queue -> work_queue

  val queue_insert : handle -> work_queue -> work_queue

  val queue_peek : work_queue -> handle option

  val queue_pop : work_queue -> (handle * work_queue) option

  type state = { sigma : store; ranking : Ranking.t; queue : work_queue;
                 started : S.t; readers : readers_table;
                 contributions : contribution_table; phases : phase_table;
                 side_phases : side_phase_table;
                 local_sides : local_side_table; controlled : S.t }

  val sigma : state -> store

  val ranking : state -> Ranking.t

  val queue : state -> work_queue

  val started : state -> S.t

  val readers : state -> readers_table

  val contributions : state -> contribution_table

  val phases : state -> phase_table

  val side_phases : state -> side_phase_table

  val local_sides : state -> local_side_table

  val controlled : state -> S.t

  val with_sigma : state -> store -> state

  val with_ranking : state -> Ranking.t -> state

  val with_queue : state -> work_queue -> state

  val with_started : state -> S.t -> state

  val with_readers : state -> readers_table -> state

  val with_contributions : state -> contribution_table -> state

  val with_phases : state -> phase_table -> state

  val with_side_phases : state -> side_phase_table -> state

  val with_local_sides : state -> local_side_table -> state

  val with_controlled : state -> S.t -> state

  val empty_state : state

  val lookup_map : 'a1 M.t M.t -> V.t -> 'a1 M.t

  val update_map : 'a1 M.t M.t -> V.t -> V.t -> 'a1 -> 'a1 M.t M.t

  val lookup_set : S.t M.t -> V.t -> S.t

  val sigma_value : state -> V.t -> D.t

  val is_materialized : state -> V.t -> bool

  val materialize : state -> V.t -> state

  val observe : state -> V.t -> state * handle

  val enqueue_handle : state -> handle -> state

  val enqueue : state -> V.t -> state

  val enqueue_all : state -> V.t list -> state

  val equivalent : D.t -> D.t -> bool

  val join_values : D.t list -> D.t

  val aggregate : state -> V.t -> D.t

  val stored_contribution : state -> V.t -> V.t -> D.t

  val stored_phase : state -> V.t -> U.phase

  val stored_side_phase : state -> V.t -> V.t -> U.phase

  val promote_controlled : state -> V.t -> state

  val add_reader : state -> V.t -> V.t -> state

  val get_ready_state : state -> handle -> handle -> state

  val reset_local_sides : state -> V.t -> state

  val start_evaluation : state -> V.t -> state

  val accumulated_side_input : state -> V.t -> V.t -> D.t -> D.t

  val record_side_payload : state -> V.t -> V.t -> D.t -> state

  val side_ready_state : state -> handle -> handle -> D.t -> state

  val write_changed_value : state -> V.t -> D.t -> state

  val set_value : state -> V.t -> D.t -> state

  val owner_may_still_be_queued : state -> handle -> bool

  type control =
  | RunLoop
  | RunSeeds of V.t list
  | RunSeedLoop of V.t list
  | RunSolveOne of handle * continuation
  | RunSolveOneLoop of handle * continuation
  | RunRhs of handle * ConstraintSystem.rhs * continuation
  | AfterGet of handle * handle * (D.t -> ConstraintSystem.rhs) * continuation
  | AfterSide of handle * ConstraintSystem.rhs * continuation
  | AfterSpawn of handle * ConstraintSystem.rhs * continuation
  and continuation =
  | KLoop
  | KSeedLoop of V.t list
  | KSolveOneLoop of handle * continuation
  | KAfterGet of handle * handle * (D.t -> ConstraintSystem.rhs)
     * continuation
  | KAfterSide of handle * ConstraintSystem.rhs * continuation
  | KAfterSpawn of handle * ConstraintSystem.rhs * continuation

  val control_rect :
    'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (handle -> continuation
    -> 'a1) -> (handle -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle -> handle -> (D.t
    -> ConstraintSystem.rhs) -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> control -> 'a1

  val control_rec :
    'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (handle -> continuation
    -> 'a1) -> (handle -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle -> handle -> (D.t
    -> ConstraintSystem.rhs) -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> control -> 'a1

  val continuation_rect :
    'a1 -> (V.t list -> 'a1) -> (handle -> continuation -> 'a1 -> 'a1) ->
    (handle -> handle -> (D.t -> ConstraintSystem.rhs) -> continuation -> 'a1
    -> 'a1) -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1)
    -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) ->
    continuation -> 'a1

  val continuation_rec :
    'a1 -> (V.t list -> 'a1) -> (handle -> continuation -> 'a1 -> 'a1) ->
    (handle -> handle -> (D.t -> ConstraintSystem.rhs) -> continuation -> 'a1
    -> 'a1) -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1)
    -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) ->
    continuation -> 'a1

  val continue : continuation -> control

  type config = { cfg_state : state; cfg_control : control }

  val cfg_state : config -> state

  val cfg_control : config -> control

  val initial_config : V.t list -> config

  val next_config : ConstraintSystem.system -> config -> config option

  val run_fuel : int -> ConstraintSystem.system -> config -> config

  val terminal_state : config -> state option

  val solve_fuel : int -> ConstraintSystem.system -> V.t list -> state option

  val solve_values_fuel :
    int -> ConstraintSystem.system -> V.t list -> store option
 end

module FixedRank :
 functor (V:VAR) ->
 functor (D:DOMAIN) ->
 functor (U:sig
  type phase

  val initial_phase : bool -> V.t -> phase

  val update : bool -> V.t -> phase -> D.t -> D.t -> phase * D.t
 end) ->
 functor (S:sig
  type t

  val empty : t

  val mem : V.t -> t -> bool

  val add : V.t -> t -> t

  val elements : t -> V.t list
 end) ->
 functor (M:sig
  type 'x t

  val empty : 'a1 t

  val lookup : 'a1 t -> V.t -> 'a1 option

  val update : 'a1 t -> V.t -> 'a1 -> 'a1 t

  val values : 'a1 t -> 'a1 list
 end) ->
 functor (Fixed:sig
  val rank : V.t -> int
 end) ->
 sig
  module Rk :
   sig
    type t = V.t list

    val empty : t

    val lookup : t -> V.t -> int option

    val size : t -> int

    val observe : t -> V.t -> t * int
   end

  module ConstraintSystem :
   sig
    type rhs =
    | Ret of D.t
    | Get of V.t * (D.t -> rhs)
    | Side of V.t * D.t * rhs
    | Spawn of V.t * rhs

    val rhs_rect :
      (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
      D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

    val rhs_rec :
      (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) -> (V.t ->
      D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1) -> rhs -> 'a1

    type system = V.t -> rhs
   end

  type store = D.t M.t

  type readers_table = S.t M.t

  type contribution_row = D.t M.t

  type contribution_table = contribution_row M.t

  type phase_table = U.phase M.t

  type side_phase_row = U.phase M.t

  type side_phase_table = side_phase_row M.t

  type local_side_row = D.t M.t

  type local_side_table = local_side_row M.t

  module Ranking :
   sig
    type t = Rk.t

    val empty : t

    val lookup : t -> V.t -> int option

    val size : t -> int

    val observe : t -> V.t -> t * int
   end

  type handle = { handle_variable : V.t; handle_rank : int }

  val handle_variable : handle -> V.t

  val handle_rank : handle -> int

  type work_queue = handle list

  val queue_contains_rank : int -> work_queue -> bool

  val queue_insert_fresh : handle -> work_queue -> work_queue

  val queue_insert : handle -> work_queue -> work_queue

  val queue_peek : work_queue -> handle option

  val queue_pop : work_queue -> (handle * work_queue) option

  type state = { sigma : store; ranking : Ranking.t; queue : work_queue;
                 started : S.t; readers : readers_table;
                 contributions : contribution_table; phases : phase_table;
                 side_phases : side_phase_table;
                 local_sides : local_side_table; controlled : S.t }

  val sigma : state -> store

  val ranking : state -> Ranking.t

  val queue : state -> work_queue

  val started : state -> S.t

  val readers : state -> readers_table

  val contributions : state -> contribution_table

  val phases : state -> phase_table

  val side_phases : state -> side_phase_table

  val local_sides : state -> local_side_table

  val controlled : state -> S.t

  val with_sigma : state -> store -> state

  val with_ranking : state -> Ranking.t -> state

  val with_queue : state -> work_queue -> state

  val with_started : state -> S.t -> state

  val with_readers : state -> readers_table -> state

  val with_contributions : state -> contribution_table -> state

  val with_phases : state -> phase_table -> state

  val with_side_phases : state -> side_phase_table -> state

  val with_local_sides : state -> local_side_table -> state

  val with_controlled : state -> S.t -> state

  val empty_state : state

  val lookup_map : 'a1 M.t M.t -> V.t -> 'a1 M.t

  val update_map : 'a1 M.t M.t -> V.t -> V.t -> 'a1 -> 'a1 M.t M.t

  val lookup_set : S.t M.t -> V.t -> S.t

  val sigma_value : state -> V.t -> D.t

  val is_materialized : state -> V.t -> bool

  val materialize : state -> V.t -> state

  val observe : state -> V.t -> state * handle

  val enqueue_handle : state -> handle -> state

  val enqueue : state -> V.t -> state

  val enqueue_all : state -> V.t list -> state

  val equivalent : D.t -> D.t -> bool

  val join_values : D.t list -> D.t

  val aggregate : state -> V.t -> D.t

  val stored_contribution : state -> V.t -> V.t -> D.t

  val stored_phase : state -> V.t -> U.phase

  val stored_side_phase : state -> V.t -> V.t -> U.phase

  val promote_controlled : state -> V.t -> state

  val add_reader : state -> V.t -> V.t -> state

  val get_ready_state : state -> handle -> handle -> state

  val reset_local_sides : state -> V.t -> state

  val start_evaluation : state -> V.t -> state

  val accumulated_side_input : state -> V.t -> V.t -> D.t -> D.t

  val record_side_payload : state -> V.t -> V.t -> D.t -> state

  val side_ready_state : state -> handle -> handle -> D.t -> state

  val write_changed_value : state -> V.t -> D.t -> state

  val set_value : state -> V.t -> D.t -> state

  val owner_may_still_be_queued : state -> handle -> bool

  type control =
  | RunLoop
  | RunSeeds of V.t list
  | RunSeedLoop of V.t list
  | RunSolveOne of handle * continuation
  | RunSolveOneLoop of handle * continuation
  | RunRhs of handle * ConstraintSystem.rhs * continuation
  | AfterGet of handle * handle * (D.t -> ConstraintSystem.rhs) * continuation
  | AfterSide of handle * ConstraintSystem.rhs * continuation
  | AfterSpawn of handle * ConstraintSystem.rhs * continuation
  and continuation =
  | KLoop
  | KSeedLoop of V.t list
  | KSolveOneLoop of handle * continuation
  | KAfterGet of handle * handle * (D.t -> ConstraintSystem.rhs)
     * continuation
  | KAfterSide of handle * ConstraintSystem.rhs * continuation
  | KAfterSpawn of handle * ConstraintSystem.rhs * continuation

  val control_rect :
    'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (handle -> continuation
    -> 'a1) -> (handle -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle -> handle -> (D.t
    -> ConstraintSystem.rhs) -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> control -> 'a1

  val control_rec :
    'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (handle -> continuation
    -> 'a1) -> (handle -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle -> handle -> (D.t
    -> ConstraintSystem.rhs) -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> (handle ->
    ConstraintSystem.rhs -> continuation -> 'a1) -> control -> 'a1

  val continuation_rect :
    'a1 -> (V.t list -> 'a1) -> (handle -> continuation -> 'a1 -> 'a1) ->
    (handle -> handle -> (D.t -> ConstraintSystem.rhs) -> continuation -> 'a1
    -> 'a1) -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1)
    -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) ->
    continuation -> 'a1

  val continuation_rec :
    'a1 -> (V.t list -> 'a1) -> (handle -> continuation -> 'a1 -> 'a1) ->
    (handle -> handle -> (D.t -> ConstraintSystem.rhs) -> continuation -> 'a1
    -> 'a1) -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1)
    -> (handle -> ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) ->
    continuation -> 'a1

  val continue : continuation -> control

  type config = { cfg_state : state; cfg_control : control }

  val cfg_state : config -> state

  val cfg_control : config -> control

  val initial_config : V.t list -> config

  val next_config : ConstraintSystem.system -> config -> config option

  val run_fuel : int -> ConstraintSystem.system -> config -> config

  val terminal_state : config -> state option

  val solve_fuel : int -> ConstraintSystem.system -> V.t list -> state option

  val solve_values_fuel :
    int -> ConstraintSystem.system -> V.t list -> store option
 end
