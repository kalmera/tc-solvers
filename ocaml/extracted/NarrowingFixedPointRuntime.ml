
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val leb : int -> int -> bool **)

let rec leb n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun m' -> leb n' m')
      m)
    n

(** val ltb : int -> int -> bool **)

let ltb n m =
  leb (Stdlib.Int.succ n) m

module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m

  (** val max : int -> int -> int **)

  let rec max n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun m' -> Stdlib.Int.succ (max n' m'))
        m)
      n
 end

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 -> let s = h y a in if s then true else in_dec h a l0

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

module type VAR =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type DOMAIN =
 sig
  type t

  val bottom : t

  val join : t -> t -> t

  val leq : t -> t -> bool
 end

module ListDiscoveryOrder =
 functor (V:VAR) ->
 struct
  type t = V.t list

  (** val empty : t **)

  let empty =
    []

  (** val lookup : t -> V.t -> int option **)

  let rec lookup order x =
    match order with
    | [] -> None
    | y :: older ->
      if V.eq_dec x y then Some (length older) else lookup older x

  (** val size : t -> int **)

  let size =
    length

  (** val observe : t -> V.t -> t * int **)

  let observe order x =
    match lookup order x with
    | Some rank -> (order, rank)
    | None -> ((x :: order), (length order))
 end

module type FEATURES =
 sig
  val restart_side_phases : bool

  val eliminate_dead_sides : bool
 end

module ListDiscoveryOrderLaws =
 functor (V:VAR) ->
 struct
  module R = ListDiscoveryOrder(V)
 end

module ListFiniteDiscoveryOrderLaws =
 functor (V:VAR) ->
 struct
  module R = ListDiscoveryOrder(V)

  module Laws = ListDiscoveryOrderLaws(V)

  module FullLaws = ListDiscoveryOrderLaws(V)

  (** val bound : V.t list -> int **)

  let bound =
    length
 end

module FirstDiscovery =
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
 functor (Features:FEATURES) ->
 functor (DL:sig
 end) ->
 functor (UL:sig
  val remaining_changes : U.phase -> D.t -> int
 end) ->
 functor (SL:sig
 end) ->
 functor (ML:sig
 end) ->
 struct
  module Rk = ListDiscoveryOrder(V)

  module Laws = ListDiscoveryOrderLaws(V)

  module Finite = ListFiniteDiscoveryOrderLaws(V)

  module Sem =
   struct
    module R =
     struct
      module ConstraintSystem =
       struct
        type rhs =
        | Ret of D.t
        | Get of V.t * (D.t -> rhs)
        | Side of V.t * D.t * rhs
        | Spawn of V.t * rhs

        (** val rhs_rect :
            (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) ->
            (V.t -> D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1)
            -> rhs -> 'a1 **)

        let rec rhs_rect f f0 f1 f2 = function
        | Ret t0 -> f t0
        | Get (t0, r0) -> f0 t0 r0 (fun t1 -> rhs_rect f f0 f1 f2 (r0 t1))
        | Side (t0, t1, r0) -> f1 t0 t1 r0 (rhs_rect f f0 f1 f2 r0)
        | Spawn (t0, r0) -> f2 t0 r0 (rhs_rect f f0 f1 f2 r0)

        (** val rhs_rec :
            (D.t -> 'a1) -> (V.t -> (D.t -> rhs) -> (D.t -> 'a1) -> 'a1) ->
            (V.t -> D.t -> rhs -> 'a1 -> 'a1) -> (V.t -> rhs -> 'a1 -> 'a1)
            -> rhs -> 'a1 **)

        let rec rhs_rec f f0 f1 f2 = function
        | Ret t0 -> f t0
        | Get (t0, r0) -> f0 t0 r0 (fun t1 -> rhs_rec f f0 f1 f2 (r0 t1))
        | Side (t0, t1, r0) -> f1 t0 t1 r0 (rhs_rec f f0 f1 f2 r0)
        | Spawn (t0, r0) -> f2 t0 r0 (rhs_rec f f0 f1 f2 r0)

        type system = V.t -> rhs
       end

      type store = D.t M.t

      type readers_table = S.t M.t

      type contribution_row = D.t M.t

      type contribution_table = contribution_row M.t

      module Ranking =
       struct
        type t = Rk.t

        (** val empty : t **)

        let empty =
          Rk.empty

        (** val lookup : t -> V.t -> int option **)

        let lookup =
          Rk.lookup

        (** val size : t -> int **)

        let size =
          Rk.size

        (** val observe : t -> V.t -> t * int **)

        let observe =
          Rk.observe
       end

      type work_queue = V.t list

      (** val ranking_lt : Ranking.t -> V.t -> V.t -> bool **)

      let ranking_lt order x y =
        match Ranking.lookup order x with
        | Some x_rank ->
          (match Ranking.lookup order y with
           | Some y_rank -> ltb x_rank y_rank
           | None -> false)
        | None -> false

      (** val queue_contains : V.t -> work_queue -> bool **)

      let rec queue_contains x = function
      | [] -> false
      | head :: rest ->
        if V.eq_dec x head then true else queue_contains x rest

      (** val queue_insert_fresh :
          Ranking.t -> V.t -> work_queue -> work_queue **)

      let rec queue_insert_fresh order x = function
      | [] -> x :: []
      | head :: rest ->
        if ranking_lt order head x
        then x :: (head :: rest)
        else head :: (queue_insert_fresh order x rest)

      (** val queue_insert : Ranking.t -> V.t -> work_queue -> work_queue **)

      let queue_insert order x q =
        if queue_contains x q then q else queue_insert_fresh order x q

      (** val queue_insert_all :
          Ranking.t -> V.t list -> work_queue -> work_queue **)

      let rec queue_insert_all order xs q =
        match xs with
        | [] -> q
        | x :: rest -> queue_insert_all order rest (queue_insert order x q)

      (** val queue_peek : work_queue -> V.t option **)

      let queue_peek = function
      | [] -> None
      | head :: _ -> Some head

      (** val queue_pop : work_queue -> (V.t * work_queue) option **)

      let queue_pop = function
      | [] -> None
      | head :: rest -> Some (head, rest)

      type side_cell = { side_phase : U.phase; side_reset_at : V.t option }

      (** val side_phase : side_cell -> U.phase **)

      let side_phase s =
        s.side_phase

      (** val side_reset_at : side_cell -> V.t option **)

      let side_reset_at s =
        s.side_reset_at

      type side_cell_row = side_cell M.t

      type side_cell_table = side_cell_row M.t

      type side_cell_id = V.t * V.t

      type reset_table = side_cell_id list M.t

      type target_table = S.t M.t

      type state = { sigma : store; ranking : Ranking.t; queue : work_queue;
                     readers : readers_table;
                     contributions : contribution_table;
                     side_cells : side_cell_table;
                     reset_at_close : reset_table;
                     last_targets : target_table; controlled : S.t }

      (** val sigma : state -> store **)

      let sigma s =
        s.sigma

      (** val ranking : state -> Ranking.t **)

      let ranking s =
        s.ranking

      (** val queue : state -> work_queue **)

      let queue s =
        s.queue

      (** val readers : state -> readers_table **)

      let readers s =
        s.readers

      (** val contributions : state -> contribution_table **)

      let contributions s =
        s.contributions

      (** val side_cells : state -> side_cell_table **)

      let side_cells s =
        s.side_cells

      (** val reset_at_close : state -> reset_table **)

      let reset_at_close s =
        s.reset_at_close

      (** val last_targets : state -> target_table **)

      let last_targets s =
        s.last_targets

      (** val controlled : state -> S.t **)

      let controlled s =
        s.controlled

      (** val empty_state : state **)

      let empty_state =
        { sigma = M.empty; ranking = Ranking.empty; queue = []; readers =
          M.empty; contributions = M.empty; side_cells = M.empty;
          reset_at_close = M.empty; last_targets = M.empty; controlled =
          S.empty }

      (** val with_sigma : state -> store -> state **)

      let with_sigma st next =
        { sigma = next; ranking = st.ranking; queue = st.queue; readers =
          st.readers; contributions = st.contributions; side_cells =
          st.side_cells; reset_at_close = st.reset_at_close; last_targets =
          st.last_targets; controlled = st.controlled }

      (** val with_ranking : state -> Ranking.t -> state **)

      let with_ranking st next =
        { sigma = st.sigma; ranking = next; queue = st.queue; readers =
          st.readers; contributions = st.contributions; side_cells =
          st.side_cells; reset_at_close = st.reset_at_close; last_targets =
          st.last_targets; controlled = st.controlled }

      (** val with_queue : state -> work_queue -> state **)

      let with_queue st next =
        { sigma = st.sigma; ranking = st.ranking; queue = next; readers =
          st.readers; contributions = st.contributions; side_cells =
          st.side_cells; reset_at_close = st.reset_at_close; last_targets =
          st.last_targets; controlled = st.controlled }

      (** val with_readers : state -> readers_table -> state **)

      let with_readers st next =
        { sigma = st.sigma; ranking = st.ranking; queue = st.queue; readers =
          next; contributions = st.contributions; side_cells = st.side_cells;
          reset_at_close = st.reset_at_close; last_targets = st.last_targets;
          controlled = st.controlled }

      (** val with_contributions : state -> contribution_table -> state **)

      let with_contributions st next =
        { sigma = st.sigma; ranking = st.ranking; queue = st.queue; readers =
          st.readers; contributions = next; side_cells = st.side_cells;
          reset_at_close = st.reset_at_close; last_targets = st.last_targets;
          controlled = st.controlled }

      (** val with_cells_and_resets :
          state -> side_cell_table -> reset_table -> state **)

      let with_cells_and_resets st cells resets =
        { sigma = st.sigma; ranking = st.ranking; queue = st.queue; readers =
          st.readers; contributions = st.contributions; side_cells = cells;
          reset_at_close = resets; last_targets = st.last_targets;
          controlled = st.controlled }

      (** val with_last_targets : state -> target_table -> state **)

      let with_last_targets st next =
        { sigma = st.sigma; ranking = st.ranking; queue = st.queue; readers =
          st.readers; contributions = st.contributions; side_cells =
          st.side_cells; reset_at_close = st.reset_at_close; last_targets =
          next; controlled = st.controlled }

      (** val with_controlled : state -> S.t -> state **)

      let with_controlled st next =
        { sigma = st.sigma; ranking = st.ranking; queue = st.queue; readers =
          st.readers; contributions = st.contributions; side_cells =
          st.side_cells; reset_at_close = st.reset_at_close; last_targets =
          st.last_targets; controlled = next }

      (** val lookup_map : 'a1 M.t M.t -> V.t -> 'a1 M.t **)

      let lookup_map table outer =
        match M.lookup table outer with
        | Some row -> row
        | None -> M.empty

      (** val update_map : 'a1 M.t M.t -> V.t -> V.t -> 'a1 -> 'a1 M.t M.t **)

      let update_map table outer inner value =
        let row = lookup_map table outer in
        M.update table outer (M.update row inner value)

      (** val lookup_set : S.t M.t -> V.t -> S.t **)

      let lookup_set table x =
        match M.lookup table x with
        | Some xs -> xs
        | None -> S.empty

      (** val lookup_reset_ids : reset_table -> V.t -> side_cell_id list **)

      let lookup_reset_ids table scope =
        match M.lookup table scope with
        | Some ids -> ids
        | None -> []

      (** val sigma_value : state -> V.t -> D.t **)

      let sigma_value st x =
        match M.lookup st.sigma x with
        | Some value -> value
        | None -> D.bottom

      (** val is_materialized : state -> V.t -> bool **)

      let is_materialized st x =
        match M.lookup st.sigma x with
        | Some _ -> true
        | None -> false

      (** val materialize : state -> V.t -> state **)

      let materialize st x =
        match M.lookup st.sigma x with
        | Some _ -> st
        | None -> with_sigma st (M.update st.sigma x D.bottom)

      (** val observe : state -> V.t -> state **)

      let observe st x =
        let (next, _) = Ranking.observe st.ranking x in with_ranking st next

      (** val rank_lt : state -> V.t -> V.t -> bool **)

      let rank_lt st x y =
        ranking_lt st.ranking x y

      (** val enqueue : state -> V.t -> state **)

      let enqueue st x =
        with_queue st (queue_insert st.ranking x st.queue)

      (** val enqueue_all : state -> V.t list -> state **)

      let enqueue_all st xs =
        with_queue st (queue_insert_all st.ranking xs st.queue)

      (** val equivalent : D.t -> D.t -> bool **)

      let equivalent left right =
        (&&) (D.leq left right) (D.leq right left)

      (** val join_values : D.t list -> D.t **)

      let rec join_values = function
      | [] -> D.bottom
      | value :: rest -> D.join value (join_values rest)

      (** val aggregate : state -> V.t -> D.t **)

      let aggregate st target =
        join_values (M.values (lookup_map st.contributions target))

      (** val stored_contribution : state -> V.t -> V.t -> D.t **)

      let stored_contribution st source target =
        match M.lookup (lookup_map st.contributions target) source with
        | Some value -> value
        | None -> D.bottom

      (** val default_side_cell : V.t -> side_cell **)

      let default_side_cell target =
        { side_phase = (U.initial_phase true target); side_reset_at = None }

      (** val stored_side_cell : state -> V.t -> V.t -> side_cell **)

      let stored_side_cell st source target =
        match M.lookup (lookup_map st.side_cells source) target with
        | Some cell -> cell
        | None -> default_side_cell target

      (** val cell_id_eq_dec : side_cell_id -> side_cell_id -> bool **)

      let cell_id_eq_dec left right =
        let (a, b) = left in
        let (t0, t1) = right in if V.eq_dec a t0 then V.eq_dec b t1 else false

      (** val remove_cell_id :
          side_cell_id -> side_cell_id list -> side_cell_id list **)

      let rec remove_cell_id id = function
      | [] -> []
      | candidate :: rest ->
        if cell_id_eq_dec id candidate
        then remove_cell_id id rest
        else candidate :: (remove_cell_id id rest)

      (** val add_cell_id :
          side_cell_id -> side_cell_id list -> side_cell_id list **)

      let add_cell_id id ids =
        if in_dec cell_id_eq_dec id ids then ids else id :: ids

      (** val remove_registration :
          reset_table -> V.t -> side_cell_id -> reset_table **)

      let remove_registration resets scope id =
        M.update resets scope
          (remove_cell_id id (lookup_reset_ids resets scope))

      (** val add_registration :
          reset_table -> V.t -> side_cell_id -> reset_table **)

      let add_registration resets scope id =
        M.update resets scope (add_cell_id id (lookup_reset_ids resets scope))

      (** val same_scope : V.t option -> V.t option -> bool **)

      let same_scope left right =
        match left with
        | Some x ->
          (match right with
           | Some y -> if V.eq_dec x y then true else false
           | None -> false)
        | None -> (match right with
                   | Some _ -> false
                   | None -> true)

      (** val register_reset :
          state -> V.t -> V.t -> V.t -> U.phase -> state **)

      let register_reset st source target scope phase0 =
        let id = (source, target) in
        let old_cell = stored_side_cell st source target in
        let eligible = rank_lt st scope target in
        let requested =
          if Features.restart_side_phases
          then if eligible then Some scope else None
          else None
        in
        let same = same_scope old_cell.side_reset_at requested in
        let without_old =
          if same
          then st.reset_at_close
          else (match old_cell.side_reset_at with
                | Some previous ->
                  remove_registration st.reset_at_close previous id
                | None -> st.reset_at_close)
        in
        let next_resets =
          if same
          then without_old
          else (match requested with
                | Some next -> add_registration without_old next id
                | None -> without_old)
        in
        let next_cell = { side_phase = phase0; side_reset_at = requested } in
        with_cells_and_resets st
          (update_map st.side_cells source target next_cell) next_resets

      (** val reset_cells :
          side_cell_id list -> side_cell_table -> side_cell_table **)

      let rec reset_cells ids cells =
        match ids with
        | [] -> cells
        | s :: rest ->
          let (source, target) = s in
          let fresh = default_side_cell target in
          reset_cells rest (update_map cells source target fresh)

      (** val reset_registered_cells : state -> V.t -> state **)

      let reset_registered_cells st owner =
        if Features.restart_side_phases
        then let ids = lookup_reset_ids st.reset_at_close owner in
             with_cells_and_resets st (reset_cells ids st.side_cells)
               (M.update st.reset_at_close owner [])
        else st

      type frame = { frame_owner : V.t; frame_phase : U.phase;
                     frame_local_side : D.t M.t;
                     frame_previous_targets : S.t;
                     frame_current_targets : S.t; frame_min_scope : V.t;
                     frame_max_read : V.t option }

      (** val frame_owner : frame -> V.t **)

      let frame_owner f =
        f.frame_owner

      (** val frame_phase : frame -> U.phase **)

      let frame_phase f =
        f.frame_phase

      (** val frame_local_side : frame -> D.t M.t **)

      let frame_local_side f =
        f.frame_local_side

      (** val frame_previous_targets : frame -> S.t **)

      let frame_previous_targets f =
        f.frame_previous_targets

      (** val frame_current_targets : frame -> S.t **)

      let frame_current_targets f =
        f.frame_current_targets

      (** val frame_min_scope : frame -> V.t **)

      let frame_min_scope f =
        f.frame_min_scope

      (** val frame_max_read : frame -> V.t option **)

      let frame_max_read f =
        f.frame_max_read

      (** val fresh_frame : state -> V.t -> U.phase -> frame **)

      let fresh_frame st owner phase0 =
        { frame_owner = owner; frame_phase = phase0; frame_local_side =
          M.empty; frame_previous_targets =
          (lookup_set st.last_targets owner); frame_current_targets =
          S.empty; frame_min_scope = owner; frame_max_read = None }

      (** val with_frame_phase : frame -> U.phase -> frame **)

      let with_frame_phase fr phase0 =
        { frame_owner = fr.frame_owner; frame_phase = phase0;
          frame_local_side = fr.frame_local_side; frame_previous_targets =
          fr.frame_previous_targets; frame_current_targets =
          fr.frame_current_targets; frame_min_scope = fr.frame_min_scope;
          frame_max_read = fr.frame_max_read }

      (** val with_frame_read : frame -> V.t -> V.t option -> frame **)

      let with_frame_read fr minimum maximum =
        { frame_owner = fr.frame_owner; frame_phase = fr.frame_phase;
          frame_local_side = fr.frame_local_side; frame_previous_targets =
          fr.frame_previous_targets; frame_current_targets =
          fr.frame_current_targets; frame_min_scope = minimum;
          frame_max_read = maximum }

      (** val with_frame_side : frame -> V.t -> D.t -> frame **)

      let with_frame_side fr target input0 =
        { frame_owner = fr.frame_owner; frame_phase = fr.frame_phase;
          frame_local_side = (M.update fr.frame_local_side target input0);
          frame_previous_targets = fr.frame_previous_targets;
          frame_current_targets = (S.add target fr.frame_current_targets);
          frame_min_scope = fr.frame_min_scope; frame_max_read =
          fr.frame_max_read }

      (** val promote_controlled : state -> V.t -> state **)

      let promote_controlled st x =
        with_controlled st (S.add x st.controlled)

      (** val complete_get :
          state -> frame -> V.t -> (state * frame) * D.t **)

      let complete_get st fr target =
        let owner = fr.frame_owner in
        let st1 =
          if rank_lt st owner target then st else promote_controlled st target
        in
        let minimum =
          if rank_lt st target fr.frame_min_scope
          then target
          else fr.frame_min_scope
        in
        let maximum =
          match fr.frame_max_read with
          | Some previous ->
            if rank_lt st previous target then Some target else Some previous
          | None -> Some target
        in
        let fr1 = with_frame_read fr minimum maximum in
        let current_readers = lookup_set st1.readers target in
        let st2 =
          with_readers st1
            (M.update st1.readers target (S.add owner current_readers))
        in
        let st3 = materialize st2 target in
        ((st3, fr1), (sigma_value st3 target))

      (** val accumulated_side_input : frame -> V.t -> D.t -> D.t **)

      let accumulated_side_input fr target raw =
        match M.lookup fr.frame_local_side target with
        | Some previous -> D.join previous raw
        | None -> raw

      (** val record_side_input : frame -> V.t -> D.t -> frame * D.t **)

      let record_side_input fr target raw =
        let input0 = accumulated_side_input fr target raw in
        ((with_frame_side fr target input0), input0)

      (** val promote_side_target : state -> frame -> V.t -> state **)

      let promote_side_target st fr target =
        let source = fr.frame_owner in
        if rank_lt st target source then st else promote_controlled st source

      (** val write_side_contribution :
          state -> frame -> V.t -> D.t -> state * bool **)

      let write_side_contribution st fr target input0 =
        let source = fr.frame_owner in
        let st1 = promote_side_target st fr target in
        let old_aggregate = aggregate st1 target in
        let old_contribution = stored_contribution st1 source target in
        let cell = stored_side_cell st1 source target in
        let updated =
          U.update true target cell.side_phase old_contribution input0
        in
        let next_phase = fst updated in
        let next_contribution = snd updated in
        let st2 =
          with_contributions st1
            (update_map st1.contributions target source next_contribution)
        in
        let st3 =
          register_reset st2 source target fr.frame_min_scope next_phase
        in
        let changed = negb (equivalent (aggregate st3 target) old_aggregate)
        in
        (st3, changed)

      (** val publish_targets : state -> frame -> state **)

      let publish_targets st fr =
        with_last_targets st
          (M.update st.last_targets fr.frame_owner fr.frame_current_targets)

      (** val set_value : state -> frame -> D.t -> state * frame **)

      let set_value st fr direct =
        let owner = fr.frame_owner in
        let candidate = D.join direct (aggregate st owner) in
        let old = sigma_value st owner in
        if equivalent candidate old
        then (st, fr)
        else let result =
               if S.mem owner st.controlled
               then U.update false owner fr.frame_phase old candidate
               else (fr.frame_phase, candidate)
             in
             let next_phase = fst result in
             let value = snd result in
             let fr1 = with_frame_phase fr next_phase in
             if equivalent value old
             then (st, fr1)
             else let st1 = with_sigma st (M.update st.sigma owner value) in
                  let invalidated = S.elements (lookup_set st1.readers owner)
                  in
                  let st2 = enqueue_all st1 invalidated in
                  let st3 =
                    with_readers st2 (M.update st2.readers owner S.empty)
                  in
                  (st3, fr1)

      (** val requeue_changed_controlled_owner :
          state -> state -> V.t -> state **)

      let requeue_changed_controlled_owner before after owner =
        with_queue after
          (if (&&) (S.mem owner before.controlled)
                (negb
                  (equivalent (sigma_value after owner)
                    (sigma_value before owner)))
           then queue_insert after.ranking owner after.queue
           else after.queue)

      type control =
      | RunLoop
      | RunSeeds of V.t list
      | RunSeedLoop of V.t list
      | StartEpisode of V.t * continuation
      | RunRhs of frame * ConstraintSystem.rhs * continuation
      | RunDead of frame * D.t * V.t list * continuation
      | RunCommit of frame * D.t * continuation
      | RunDrain of frame * continuation
      | Return of continuation
      and continuation =
      | KLoop
      | KSeedLoop of V.t list
      | KAfterGet of frame * V.t * (D.t -> ConstraintSystem.rhs)
         * continuation
      | KAfterSide of frame * ConstraintSystem.rhs * continuation
      | KAfterSpawn of frame * ConstraintSystem.rhs * continuation
      | KDead of frame * D.t * V.t list * continuation
      | KDrain of frame * continuation

      (** val control_rect :
          'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (V.t ->
          continuation -> 'a1) -> (frame -> ConstraintSystem.rhs ->
          continuation -> 'a1) -> (frame -> D.t -> V.t list -> continuation
          -> 'a1) -> (frame -> D.t -> continuation -> 'a1) -> (frame ->
          continuation -> 'a1) -> (continuation -> 'a1) -> control -> 'a1 **)

      let control_rect f f0 f1 f2 f3 f4 f5 f6 f7 = function
      | RunLoop -> f
      | RunSeeds l -> f0 l
      | RunSeedLoop l -> f1 l
      | StartEpisode (t0, c0) -> f2 t0 c0
      | RunRhs (f8, r, c0) -> f3 f8 r c0
      | RunDead (f8, t0, l, c0) -> f4 f8 t0 l c0
      | RunCommit (f8, t0, c0) -> f5 f8 t0 c0
      | RunDrain (f8, c0) -> f6 f8 c0
      | Return c0 -> f7 c0

      (** val control_rec :
          'a1 -> (V.t list -> 'a1) -> (V.t list -> 'a1) -> (V.t ->
          continuation -> 'a1) -> (frame -> ConstraintSystem.rhs ->
          continuation -> 'a1) -> (frame -> D.t -> V.t list -> continuation
          -> 'a1) -> (frame -> D.t -> continuation -> 'a1) -> (frame ->
          continuation -> 'a1) -> (continuation -> 'a1) -> control -> 'a1 **)

      let control_rec f f0 f1 f2 f3 f4 f5 f6 f7 = function
      | RunLoop -> f
      | RunSeeds l -> f0 l
      | RunSeedLoop l -> f1 l
      | StartEpisode (t0, c0) -> f2 t0 c0
      | RunRhs (f8, r, c0) -> f3 f8 r c0
      | RunDead (f8, t0, l, c0) -> f4 f8 t0 l c0
      | RunCommit (f8, t0, c0) -> f5 f8 t0 c0
      | RunDrain (f8, c0) -> f6 f8 c0
      | Return c0 -> f7 c0

      (** val continuation_rect :
          'a1 -> (V.t list -> 'a1) -> (frame -> V.t -> (D.t ->
          ConstraintSystem.rhs) -> continuation -> 'a1 -> 'a1) -> (frame ->
          ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) -> (frame ->
          ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) -> (frame ->
          D.t -> V.t list -> continuation -> 'a1 -> 'a1) -> (frame ->
          continuation -> 'a1 -> 'a1) -> continuation -> 'a1 **)

      let rec continuation_rect f f0 f1 f2 f3 f4 f5 = function
      | KLoop -> f
      | KSeedLoop l -> f0 l
      | KAfterGet (f6, t0, r, c0) ->
        f1 f6 t0 r c0 (continuation_rect f f0 f1 f2 f3 f4 f5 c0)
      | KAfterSide (f6, r, c0) ->
        f2 f6 r c0 (continuation_rect f f0 f1 f2 f3 f4 f5 c0)
      | KAfterSpawn (f6, r, c0) ->
        f3 f6 r c0 (continuation_rect f f0 f1 f2 f3 f4 f5 c0)
      | KDead (f6, t0, l, c0) ->
        f4 f6 t0 l c0 (continuation_rect f f0 f1 f2 f3 f4 f5 c0)
      | KDrain (f6, c0) -> f5 f6 c0 (continuation_rect f f0 f1 f2 f3 f4 f5 c0)

      (** val continuation_rec :
          'a1 -> (V.t list -> 'a1) -> (frame -> V.t -> (D.t ->
          ConstraintSystem.rhs) -> continuation -> 'a1 -> 'a1) -> (frame ->
          ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) -> (frame ->
          ConstraintSystem.rhs -> continuation -> 'a1 -> 'a1) -> (frame ->
          D.t -> V.t list -> continuation -> 'a1 -> 'a1) -> (frame ->
          continuation -> 'a1 -> 'a1) -> continuation -> 'a1 **)

      let rec continuation_rec f f0 f1 f2 f3 f4 f5 = function
      | KLoop -> f
      | KSeedLoop l -> f0 l
      | KAfterGet (f6, t0, r, c0) ->
        f1 f6 t0 r c0 (continuation_rec f f0 f1 f2 f3 f4 f5 c0)
      | KAfterSide (f6, r, c0) ->
        f2 f6 r c0 (continuation_rec f f0 f1 f2 f3 f4 f5 c0)
      | KAfterSpawn (f6, r, c0) ->
        f3 f6 r c0 (continuation_rec f f0 f1 f2 f3 f4 f5 c0)
      | KDead (f6, t0, l, c0) ->
        f4 f6 t0 l c0 (continuation_rec f f0 f1 f2 f3 f4 f5 c0)
      | KDrain (f6, c0) -> f5 f6 c0 (continuation_rec f f0 f1 f2 f3 f4 f5 c0)

      type config = { cfg_state : state; cfg_control : control }

      (** val cfg_state : config -> state **)

      let cfg_state c =
        c.cfg_state

      (** val cfg_control : config -> control **)

      let cfg_control c =
        c.cfg_control

      (** val initial_config : V.t list -> config **)

      let initial_config initial =
        { cfg_state = empty_state; cfg_control = (RunSeeds initial) }

      (** val continue_side :
          state -> frame -> V.t -> ConstraintSystem.rhs -> continuation ->
          bool -> config **)

      let continue_side st fr target next k = function
      | true ->
        if (&&) (rank_lt st fr.frame_owner target)
             (negb (is_materialized st target))
        then { cfg_state = st; cfg_control = (StartEpisode (target,
               (KAfterSide (fr, next, k)))) }
        else { cfg_state = (enqueue st target); cfg_control = (RunRhs (fr,
               next, k)) }
      | false -> { cfg_state = st; cfg_control = (RunRhs (fr, next, k)) }

      (** val continue_dead :
          state -> frame -> D.t -> V.t -> V.t list -> continuation -> bool ->
          config **)

      let continue_dead st fr direct target remaining k = function
      | true ->
        if (&&) (rank_lt st fr.frame_owner target)
             (negb (is_materialized st target))
        then { cfg_state = st; cfg_control = (StartEpisode (target, (KDead
               (fr, direct, remaining, k)))) }
        else { cfg_state = (enqueue st target); cfg_control = (RunDead (fr,
               direct, remaining, k)) }
      | false ->
        { cfg_state = st; cfg_control = (RunDead (fr, direct, remaining, k)) }

      (** val next_config :
          ConstraintSystem.system -> config -> config option **)

      let next_config tf c =
        let st = c.cfg_state in
        (match c.cfg_control with
         | RunLoop ->
           (match queue_pop st.queue with
            | Some p ->
              let (owner, rest) = p in
              Some { cfg_state = (with_queue st rest); cfg_control =
              (StartEpisode (owner, KLoop)) }
            | None -> None)
         | RunSeeds roots ->
           (match roots with
            | [] -> Some { cfg_state = st; cfg_control = RunLoop }
            | root :: remaining ->
              let st1 = observe st root in
              if is_materialized st1 root
              then Some { cfg_state = st1; cfg_control = (RunSeeds
                     remaining) }
              else Some { cfg_state = st1; cfg_control = (StartEpisode (root,
                     (KSeedLoop remaining))) })
         | RunSeedLoop remaining ->
           (match queue_pop st.queue with
            | Some p ->
              let (owner, rest) = p in
              Some { cfg_state = (with_queue st rest); cfg_control =
              (StartEpisode (owner, (KSeedLoop remaining))) }
            | None ->
              Some { cfg_state = st; cfg_control = (RunSeeds remaining) })
         | StartEpisode (owner, k) ->
           let st1 = materialize st owner in
           let phase0 = U.initial_phase false owner in
           Some { cfg_state = st1; cfg_control = (RunRhs
           ((fresh_frame st1 owner phase0), (tf owner), k)) }
         | RunRhs (fr, body, k) ->
           (match body with
            | ConstraintSystem.Ret direct ->
              Some { cfg_state = st; cfg_control = (RunDead (fr, direct,
                (if Features.eliminate_dead_sides
                 then S.elements fr.frame_previous_targets
                 else []),
                k)) }
            | ConstraintSystem.Get (target, kget) ->
              let st0 = observe st target in
              if (&&) (negb (is_materialized st0 target))
                   (rank_lt st0 fr.frame_owner target)
              then Some { cfg_state = st0; cfg_control = (StartEpisode
                     (target, (KAfterGet (fr, target, kget, k)))) }
              else let st1 =
                     if is_materialized st0 target
                     then st0
                     else enqueue st0 target
                   in
                   let (p, value) = complete_get st1 fr target in
                   let (st2, fr1) = p in
                   Some { cfg_state = st2; cfg_control = (RunRhs (fr1,
                   (kget value), k)) }
            | ConstraintSystem.Side (target, raw, next) ->
              let st0 = observe st target in
              let (fr1, input0) = record_side_input fr target raw in
              let (st1, changed) =
                write_side_contribution st0 fr1 target input0
              in
              Some (continue_side st1 fr1 target next k changed)
            | ConstraintSystem.Spawn (target, next) ->
              let st0 = observe st target in
              if is_materialized st0 target
              then Some { cfg_state = st0; cfg_control = (RunRhs (fr, next,
                     k)) }
              else if rank_lt st0 fr.frame_owner target
                   then Some { cfg_state = st0; cfg_control = (StartEpisode
                          (target, (KAfterSpawn (fr, next, k)))) }
                   else Some { cfg_state =
                          (materialize (enqueue st0 target) target);
                          cfg_control = (RunRhs (fr, next, k)) })
         | RunDead (fr, direct, pending, k) ->
           (match pending with
            | [] ->
              Some { cfg_state = (publish_targets st fr); cfg_control =
                (RunCommit (fr, direct, k)) }
            | target :: remaining ->
              if S.mem target fr.frame_current_targets
              then Some { cfg_state = st; cfg_control = (RunDead (fr, direct,
                     remaining, k)) }
              else let (st1, changed) =
                     write_side_contribution st fr target D.bottom
                   in
                   Some
                   (continue_dead st1 fr direct target remaining k changed))
         | RunCommit (fr, direct, k) ->
           let (st1, fr1) = set_value st fr direct in
           Some { cfg_state =
           (requeue_changed_controlled_owner st st1 fr.frame_owner);
           cfg_control = (RunDrain (fr1, k)) }
         | RunDrain (fr, k) ->
           (match queue_peek st.queue with
            | Some next ->
              if V.eq_dec next fr.frame_owner
              then (match queue_pop st.queue with
                    | Some p ->
                      let (_, rest) = p in
                      let st1 = with_queue st rest in
                      Some { cfg_state = st1; cfg_control = (RunRhs
                      ((fresh_frame st1 fr.frame_owner fr.frame_phase),
                      (tf fr.frame_owner), k)) }
                    | None -> None)
              else if rank_lt st fr.frame_owner next
                   then (match queue_pop st.queue with
                         | Some p ->
                           let (_, rest) = p in
                           Some { cfg_state = (with_queue st rest);
                           cfg_control = (StartEpisode (next, (KDrain (fr,
                           k)))) }
                         | None -> None)
                   else Some { cfg_state =
                          (reset_registered_cells st fr.frame_owner);
                          cfg_control = (Return k) }
            | None ->
              Some { cfg_state = (reset_registered_cells st fr.frame_owner);
                cfg_control = (Return k) })
         | Return k ->
           (match k with
            | KLoop -> Some { cfg_state = st; cfg_control = RunLoop }
            | KSeedLoop remaining ->
              Some { cfg_state = st; cfg_control = (RunSeedLoop remaining) }
            | KAfterGet (fr, target, kget, k') ->
              let (p, value) = complete_get st fr target in
              let (st1, fr1) = p in
              Some { cfg_state = st1; cfg_control = (RunRhs (fr1,
              (kget value), k')) }
            | KAfterSide (fr, next, k') ->
              Some { cfg_state = st; cfg_control = (RunRhs (fr, next, k')) }
            | KAfterSpawn (fr, next, k') ->
              Some { cfg_state = st; cfg_control = (RunRhs (fr, next, k')) }
            | KDead (fr, direct, remaining, k') ->
              Some { cfg_state = st; cfg_control = (RunDead (fr, direct,
                remaining, k')) }
            | KDrain (fr, k') ->
              Some { cfg_state = st; cfg_control = (RunDrain (fr, k')) }))

      (** val run_fuel :
          int -> ConstraintSystem.system -> config -> config **)

      let rec run_fuel fuel tf c =
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> c)
          (fun remaining ->
          match next_config tf c with
          | Some next -> run_fuel remaining tf next
          | None -> c)
          fuel

      (** val terminal_state : config -> state option **)

      let terminal_state c =
        match c.cfg_control with
        | RunLoop ->
          (match queue_peek c.cfg_state.queue with
           | Some _ -> None
           | None -> Some c.cfg_state)
        | _ -> None

      (** val solve_fuel :
          int -> ConstraintSystem.system -> V.t list -> state option **)

      let solve_fuel fuel tf initial =
        terminal_state (run_fuel fuel tf (initial_config initial))
     end

    module ConstraintSyntax =
     struct
      type rhs = R.ConstraintSystem.rhs

      (** val coq_Ret : D.t -> R.ConstraintSystem.rhs **)

      let coq_Ret x =
        R.ConstraintSystem.Ret x

      (** val coq_Get :
          V.t -> (D.t -> R.ConstraintSystem.rhs) -> R.ConstraintSystem.rhs **)

      let coq_Get x x0 =
        R.ConstraintSystem.Get (x, x0)

      (** val coq_Side :
          V.t -> D.t -> R.ConstraintSystem.rhs -> R.ConstraintSystem.rhs **)

      let coq_Side x x0 x1 =
        R.ConstraintSystem.Side (x, x0, x1)

      (** val coq_Spawn :
          V.t -> R.ConstraintSystem.rhs -> R.ConstraintSystem.rhs **)

      let coq_Spawn x x0 =
        R.ConstraintSystem.Spawn (x, x0)

      type system = V.t -> rhs
     end

    module ConstraintSemantics =
     struct
      module Observation =
       struct
        type valuation = V.t -> D.t

        type observation = { observed_direct : D.t;
                             observed_reads : (V.t * D.t) list;
                             observed_sides : (V.t * D.t) list;
                             observed_spawns : V.t list }

        (** val observed_direct : observation -> D.t **)

        let observed_direct o =
          o.observed_direct

        (** val observed_reads : observation -> (V.t * D.t) list **)

        let observed_reads o =
          o.observed_reads

        (** val observed_sides : observation -> (V.t * D.t) list **)

        let observed_sides o =
          o.observed_sides

        (** val observed_spawns : observation -> V.t list **)

        let observed_spawns o =
          o.observed_spawns
       end

      type valuation = Observation.valuation

      type observation = Observation.observation

      (** val observed_direct : Observation.observation -> D.t **)

      let observed_direct o =
        o.Observation.observed_direct

      (** val observed_reads : Observation.observation -> (V.t * D.t) list **)

      let observed_reads o =
        o.Observation.observed_reads

      (** val observed_sides : Observation.observation -> (V.t * D.t) list **)

      let observed_sides o =
        o.Observation.observed_sides

      (** val observed_spawns : Observation.observation -> V.t list **)

      let observed_spawns o =
        o.Observation.observed_spawns

      type finite_system =
        V.t list
        (* singleton inductive, whose constructor was Build_finite_system *)

      (** val support :
          ConstraintSyntax.system -> V.t list -> finite_system -> V.t list **)

      let support _ _ f =
        f
     end

    module Observation = ConstraintSemantics.Observation

    type valuation = Observation.valuation

    type observation = Observation.observation

    (** val observed_direct : Observation.observation -> D.t **)

    let observed_direct =
      Observation.observed_direct

    (** val observed_reads : Observation.observation -> (V.t * D.t) list **)

    let observed_reads =
      Observation.observed_reads

    (** val observed_sides : Observation.observation -> (V.t * D.t) list **)

    let observed_sides =
      Observation.observed_sides

    (** val observed_spawns : Observation.observation -> V.t list **)

    let observed_spawns =
      Observation.observed_spawns

    type finite_system =
      V.t list
      (* singleton inductive, whose constructor was Build_finite_system *)

    (** val support :
        ConstraintSyntax.system -> V.t list -> finite_system -> V.t list **)

    let support _ _ f =
      f

    (** val terminal_config : R.state -> R.config **)

    let terminal_config st =
      { R.cfg_state = st; R.cfg_control = R.RunLoop }

    (** val state_valuation : R.state -> valuation **)

    let state_valuation =
      R.sigma_value
   end

  module R = Sem.R

  (** val unobserved_budget : V.t list -> R.state -> int **)

  let rec unobserved_budget support0 st =
    match support0 with
    | [] -> 0
    | x :: rest ->
      (match R.Ranking.lookup (R.ranking st) x with
       | Some _ -> unobserved_budget rest st
       | None -> Stdlib.Int.succ (unobserved_budget rest st))

  module SeedMeasure =
   struct
    (** val continuation_seed_measure : R.continuation -> int **)

    let rec continuation_seed_measure = function
    | R.KLoop -> 0
    | R.KSeedLoop roots ->
      add (mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) (length roots))
        (Stdlib.Int.succ (Stdlib.Int.succ 0))
    | R.KAfterGet (_, _, _, rest) -> continuation_seed_measure rest
    | R.KAfterSide (_, _, rest) -> continuation_seed_measure rest
    | R.KAfterSpawn (_, _, rest) -> continuation_seed_measure rest
    | R.KDead (_, _, _, rest) -> continuation_seed_measure rest
    | R.KDrain (_, rest) -> continuation_seed_measure rest

    (** val seed_measure : R.control -> int **)

    let seed_measure = function
    | R.RunLoop -> 0
    | R.RunSeeds roots ->
      add (mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) (length roots))
        (Stdlib.Int.succ 0)
    | R.RunSeedLoop roots ->
      add (mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) (length roots))
        (Stdlib.Int.succ (Stdlib.Int.succ 0))
    | R.StartEpisode (_, rest) -> continuation_seed_measure rest
    | R.RunRhs (_, _, rest) -> continuation_seed_measure rest
    | R.RunDead (_, _, _, rest) -> continuation_seed_measure rest
    | R.RunCommit (_, _, rest) -> continuation_seed_measure rest
    | R.RunDrain (_, rest) -> continuation_seed_measure rest
    | R.Return rest -> continuation_seed_measure rest
   end

  (** val higher_count : R.state -> V.t list -> V.t -> int **)

  let higher_count st support0 owner =
    length (filter (fun x -> R.rank_lt st owner x) support0)

  type local_work =
  | WorkEval of R.ConstraintSystem.rhs
  | WorkAfterGet of V.t * (D.t -> R.ConstraintSystem.rhs)
  | WorkDead of int
  | WorkCommit
  | WorkDrain
  | WorkFinish

  (** val local_work_rect :
      (R.ConstraintSystem.rhs -> 'a1) -> (V.t -> (D.t ->
      R.ConstraintSystem.rhs) -> 'a1) -> (int -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
      local_work -> 'a1 **)

  let local_work_rect f f0 f1 f2 f3 f4 = function
  | WorkEval r -> f r
  | WorkAfterGet (t0, r) -> f0 t0 r
  | WorkDead n -> f1 n
  | WorkCommit -> f2
  | WorkDrain -> f3
  | WorkFinish -> f4

  (** val local_work_rec :
      (R.ConstraintSystem.rhs -> 'a1) -> (V.t -> (D.t ->
      R.ConstraintSystem.rhs) -> 'a1) -> (int -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
      local_work -> 'a1 **)

  let local_work_rec f f0 f1 f2 f3 f4 = function
  | WorkEval r -> f r
  | WorkAfterGet (t0, r) -> f0 t0 r
  | WorkDead n -> f1 n
  | WorkCommit -> f2
  | WorkDrain -> f3
  | WorkFinish -> f4

  type owner_work = V.t * local_work

  (** val continuation_work : R.continuation -> owner_work list **)

  let rec continuation_work = function
  | R.KAfterGet (fr, target, next, rest) ->
    ((R.frame_owner fr), (WorkAfterGet (target,
      next))) :: (continuation_work rest)
  | R.KAfterSide (fr, next, rest) ->
    ((R.frame_owner fr), (WorkEval next)) :: (continuation_work rest)
  | R.KAfterSpawn (fr, next, rest) ->
    ((R.frame_owner fr), (WorkEval next)) :: (continuation_work rest)
  | R.KDead (fr, _, pending, rest) ->
    ((R.frame_owner fr), (WorkDead
      (length pending))) :: (continuation_work rest)
  | R.KDrain (fr, rest) ->
    ((R.frame_owner fr), WorkDrain) :: (continuation_work rest)
  | _ -> []

  (** val control_work :
      R.ConstraintSystem.system -> R.control -> owner_work list **)

  let control_work tf = function
  | R.StartEpisode (owner, k) ->
    (owner, (WorkEval (tf owner))) :: (continuation_work k)
  | R.RunRhs (fr, body, k) ->
    ((R.frame_owner fr), (WorkEval body)) :: (continuation_work k)
  | R.RunDead (fr, _, pending, k) ->
    ((R.frame_owner fr), (WorkDead (length pending))) :: (continuation_work k)
  | R.RunCommit (fr, _, k) ->
    ((R.frame_owner fr), WorkCommit) :: (continuation_work k)
  | R.RunDrain (fr, k) ->
    ((R.frame_owner fr), WorkDrain) :: (continuation_work k)
  | R.Return k -> continuation_work k
  | _ -> []

  module Credits =
   struct
    (** val side_cell_credit : R.state -> V.t -> V.t -> int **)

    let side_cell_credit st source target =
      UL.remaining_changes
        (R.side_phase (R.stored_side_cell st source target))
        (R.stored_contribution st source target)

    (** val ordinary_credit : R.state -> R.frame -> int **)

    let ordinary_credit st fr =
      UL.remaining_changes (R.frame_phase fr)
        (R.sigma_value st (R.frame_owner fr))

    (** val source_side_credit : V.t list -> R.state -> V.t -> int **)

    let rec source_side_credit support0 st source =
      match support0 with
      | [] -> 0
      | target :: rest ->
        add (side_cell_credit st source target)
          (source_side_credit rest st source)

    (** val total_side_credit_for : V.t list -> V.t list -> R.state -> int **)

    let rec total_side_credit_for targets sources st =
      match sources with
      | [] -> 0
      | source :: rest ->
        add (source_side_credit targets st source)
          (total_side_credit_for targets rest st)

    (** val total_side_credit : V.t list -> R.state -> int **)

    let total_side_credit support0 st =
      total_side_credit_for support0 support0 st
   end

  module ScopeBounds =
   struct
   end

  module ReaderOrder =
   struct
   end

  module Termination =
   struct
    (** val unmaterialized_count : V.t list -> R.state -> int **)

    let rec unmaterialized_count support0 st =
      match support0 with
      | [] -> 0
      | x :: rest ->
        add (if R.is_materialized st x then 0 else Stdlib.Int.succ 0)
          (unmaterialized_count rest st)

    (** val continuation_containsb : V.t -> R.continuation -> bool **)

    let rec continuation_containsb owner = function
    | R.KAfterGet (fr, _, _, rest) ->
      if V.eq_dec owner (R.frame_owner fr)
      then true
      else continuation_containsb owner rest
    | R.KAfterSide (fr, _, rest) ->
      if V.eq_dec owner (R.frame_owner fr)
      then true
      else continuation_containsb owner rest
    | R.KAfterSpawn (fr, _, rest) ->
      if V.eq_dec owner (R.frame_owner fr)
      then true
      else continuation_containsb owner rest
    | R.KDead (fr, _, _, rest) ->
      if V.eq_dec owner (R.frame_owner fr)
      then true
      else continuation_containsb owner rest
    | R.KDrain (fr, rest) ->
      if V.eq_dec owner (R.frame_owner fr)
      then true
      else continuation_containsb owner rest
    | _ -> false

    (** val control_containsb : V.t -> R.control -> bool **)

    let control_containsb owner = function
    | R.StartEpisode (current, k) ->
      if V.eq_dec owner current then true else continuation_containsb owner k
    | R.RunRhs (fr, _, k) ->
      if V.eq_dec owner (R.frame_owner fr)
      then true
      else continuation_containsb owner k
    | R.RunDead (fr, _, _, k) ->
      if V.eq_dec owner (R.frame_owner fr)
      then true
      else continuation_containsb owner k
    | R.RunCommit (fr, _, k) ->
      if V.eq_dec owner (R.frame_owner fr)
      then true
      else continuation_containsb owner k
    | R.RunDrain (fr, k) ->
      if V.eq_dec owner (R.frame_owner fr)
      then true
      else continuation_containsb owner k
    | R.Return k -> continuation_containsb owner k
    | _ -> false

    (** val owner_commitb : V.t -> R.config -> bool **)

    let owner_commitb owner c =
      match R.cfg_control c with
      | R.RunCommit (fr, _, _) ->
        if V.eq_dec (R.frame_owner fr) owner then true else false
      | _ -> false

    (** val promotion_reserve : R.state -> V.t -> int **)

    let promotion_reserve st owner =
      if S.mem owner (R.controlled st) then 0 else Stdlib.Int.succ 0

    (** val target_side_credit : V.t list -> R.state -> V.t -> int **)

    let rec target_side_credit support0 st target =
      match support0 with
      | [] -> 0
      | source :: rest ->
        add (Credits.side_cell_credit st source target)
          (target_side_credit rest st target)

    (** val continuation_frame : V.t -> R.continuation -> R.frame option **)

    let rec continuation_frame owner = function
    | R.KAfterGet (fr, _, _, rest) ->
      if V.eq_dec (R.frame_owner fr) owner
      then Some fr
      else continuation_frame owner rest
    | R.KAfterSide (fr, _, rest) ->
      if V.eq_dec (R.frame_owner fr) owner
      then Some fr
      else continuation_frame owner rest
    | R.KAfterSpawn (fr, _, rest) ->
      if V.eq_dec (R.frame_owner fr) owner
      then Some fr
      else continuation_frame owner rest
    | R.KDead (fr, _, _, rest) ->
      if V.eq_dec (R.frame_owner fr) owner
      then Some fr
      else continuation_frame owner rest
    | R.KDrain (fr, rest) ->
      if V.eq_dec (R.frame_owner fr) owner
      then Some fr
      else continuation_frame owner rest
    | _ -> None

    (** val control_frame : V.t -> R.control -> R.frame option **)

    let control_frame owner = function
    | R.StartEpisode (current, k) ->
      if V.eq_dec current owner then None else continuation_frame owner k
    | R.RunRhs (fr, _, k) ->
      if V.eq_dec (R.frame_owner fr) owner
      then Some fr
      else continuation_frame owner k
    | R.RunDead (fr, _, _, k) ->
      if V.eq_dec (R.frame_owner fr) owner
      then Some fr
      else continuation_frame owner k
    | R.RunCommit (fr, _, k) ->
      if V.eq_dec (R.frame_owner fr) owner
      then Some fr
      else continuation_frame owner k
    | R.RunDrain (fr, k) ->
      if V.eq_dec (R.frame_owner fr) owner
      then Some fr
      else continuation_frame owner k
    | R.Return k -> continuation_frame owner k
    | _ -> None

    (** val active_ordinary_credit : R.state -> R.control -> V.t -> int **)

    let active_ordinary_credit st control0 owner =
      if S.mem owner (R.controlled st)
      then (match control_frame owner control0 with
            | Some fr -> Credits.ordinary_credit st fr
            | None -> 0)
      else 0

    (** val owner_round_measure :
        V.t list -> int -> V.t -> R.config ->
        int * (int * (int * (int * (int * int)))) **)

    let owner_round_measure support0 first_round owner c =
      (first_round, ((unmaterialized_count support0 (R.cfg_state c)),
        ((promotion_reserve (R.cfg_state c) owner),
        ((Credits.source_side_credit support0 (R.cfg_state c) owner),
        ((target_side_credit support0 (R.cfg_state c) owner),
        (active_ordinary_credit (R.cfg_state c) (R.cfg_control c) owner))))))

    (** val executed_rerun :
        R.ConstraintSystem.system -> V.t -> R.continuation -> R.state ->
        R.frame -> R.work_queue -> R.config **)

    let executed_rerun tf owner k before fr tail =
      { R.cfg_state = (R.with_queue before tail); R.cfg_control = (R.RunRhs
        ((R.fresh_frame (R.with_queue before tail) owner (R.frame_phase fr)),
        (tf owner), k)) }

    (** val base_continuation : V.t list option -> R.continuation **)

    let base_continuation = function
    | Some rest -> R.KSeedLoop rest
    | None -> R.KLoop

    (** val base_control : V.t list option -> R.control **)

    let base_control = function
    | Some rest -> R.RunSeedLoop rest
    | None -> R.RunLoop
   end

  (** val commit_value : R.state -> V.t -> D.t -> R.state **)

  let commit_value st owner value =
    let st1 = R.with_sigma st (M.update (R.sigma st) owner value) in
    let invalidated = S.elements (R.lookup_set (R.readers st1) owner) in
    let st2 = R.enqueue_all st1 invalidated in
    R.with_readers st2 (M.update (R.readers st2) owner S.empty)

  (** val add_reader : R.state -> V.t -> V.t -> R.state **)

  let add_reader st target owner =
    R.with_readers st
      (M.update (R.readers st) target
        (S.add owner (R.lookup_set (R.readers st) target)))
 end

module PreCommit =
 struct
  module Make =
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
   functor (Features:FEATURES) ->
   functor (DL:sig
   end) ->
   functor (UL:sig
    val remaining_changes : U.phase -> D.t -> int
   end) ->
   functor (SL:sig
   end) ->
   functor (ML:sig
   end) ->
   struct
    module Base = FirstDiscovery(V)(D)(U)(S)(M)(Features)(DL)(UL)(SL)(ML)

    module R = Base.R

    (** val pending_above : R.state -> V.t -> (V.t * R.work_queue) option **)

    let pending_above st owner =
      if S.mem owner (R.controlled st)
      then (match R.queue_pop (R.queue st) with
            | Some p ->
              let (target, rest) = p in
              if R.rank_lt st owner target then Some (target, rest) else None
            | None -> None)
      else None

    (** val suspend_commit :
        R.ConstraintSystem.system -> R.state -> R.frame -> R.continuation ->
        V.t -> R.work_queue -> R.config **)

    let suspend_commit tf st fr k target rest =
      { R.cfg_state = (R.with_queue st rest); R.cfg_control = (R.StartEpisode
        (target, (R.KAfterSide
        ((R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr)),
        (tf (R.frame_owner fr)), k)))) }

    (** val next_config :
        R.ConstraintSystem.system -> R.config -> R.config option **)

    let next_config tf c =
      match R.cfg_control c with
      | R.RunCommit (fr, _, k) ->
        (match pending_above (R.cfg_state c) (R.frame_owner fr) with
         | Some p ->
           let (target, rest) = p in
           Some (suspend_commit tf (R.cfg_state c) fr k target rest)
         | None -> R.next_config tf c)
      | _ -> R.next_config tf c

    (** val publish_accumulated :
        V.t list -> R.state -> R.frame -> R.state **)

    let rec publish_accumulated targets st fr =
      match targets with
      | [] -> st
      | target :: rest ->
        let input0 =
          match M.lookup (R.frame_local_side fr) target with
          | Some value -> value
          | None -> D.bottom
        in
        let (next, changed) = R.write_side_contribution st fr target input0 in
        publish_accumulated rest
          (if changed then R.enqueue next target else next) fr

    (** val next_batched :
        R.ConstraintSystem.system -> R.config -> R.config option **)

    let next_batched tf c =
      let st = R.cfg_state c in
      (match R.cfg_control c with
       | R.RunRhs (fr, r, k) ->
         (match r with
          | R.ConstraintSystem.Side (target, raw, body) ->
            let (next_fr, _) = R.record_side_input fr target raw in
            Some { R.cfg_state = (R.observe st target); R.cfg_control =
            (R.RunRhs (next_fr, body, k)) }
          | _ -> next_config tf c)
       | R.RunDead (fr, direct, l, k) ->
         (match l with
          | [] ->
            let next =
              publish_accumulated (S.elements (R.frame_current_targets fr))
                st fr
            in
            Some { R.cfg_state = (R.publish_targets next fr); R.cfg_control =
            (R.RunCommit (fr, direct, k)) }
          | _ :: _ -> next_config tf c)
       | _ -> next_config tf c)

    (** val clear_owner : R.state -> V.t -> R.state **)

    let clear_owner st owner =
      R.with_queue st
        (filter (fun x -> if V.eq_dec x owner then false else true)
          (R.queue st))

    (** val retry_current :
        R.ConstraintSystem.system -> R.state -> R.frame -> R.continuation ->
        R.config **)

    let retry_current tf st fr k =
      let current = clear_owner st (R.frame_owner fr) in
      { R.cfg_state = current; R.cfg_control = (R.RunRhs
      ((R.fresh_frame current (R.frame_owner fr) (R.frame_phase fr)),
      (tf (R.frame_owner fr)), k)) }

    (** val next_fresh :
        R.ConstraintSystem.system -> R.config -> R.config option **)

    let next_fresh tf c =
      let st = R.cfg_state c in
      (match R.cfg_control c with
       | R.StartEpisode (owner, k) ->
         next_batched tf { R.cfg_state = (clear_owner st owner);
           R.cfg_control = (R.StartEpisode (owner, k)) }
       | R.RunCommit (fr, _, k) ->
         (match pending_above st (R.frame_owner fr) with
          | Some p ->
            let (target, rest) = p in
            Some (suspend_commit tf st fr k target rest)
          | None ->
            if R.queue_contains (R.frame_owner fr) (R.queue st)
            then Some (retry_current tf st fr k)
            else next_batched tf c)
       | R.Return c0 ->
         (match c0 with
          | R.KAfterSide (fr, body, k) ->
            next_batched tf { R.cfg_state =
              (clear_owner st (R.frame_owner fr)); R.cfg_control = (R.Return
              (R.KAfterSide (fr, body, k))) }
          | _ -> next_batched tf c)
       | _ -> next_batched tf c)
   end
 end

module ReadHistory =
 struct
  module Make =
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
   functor (Features:FEATURES) ->
   functor (DL:sig
   end) ->
   functor (UL:sig
    val remaining_changes : U.phase -> D.t -> int
   end) ->
   functor (SL:sig
   end) ->
   functor (ML:sig
   end) ->
   struct
    module P = PreCommit.Make(V)(D)(U)(S)(M)(Features)(DL)(UL)(SL)(ML)

    module B = P.Base

    module R = P.R

    module T = B.Termination
   end
 end

module CellRepair =
 struct
  module Make =
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
   functor (Features:FEATURES) ->
   functor (DL:sig
   end) ->
   functor (UL:sig
    val remaining_changes : U.phase -> D.t -> int
   end) ->
   functor (SL:sig
   end) ->
   functor (ML:sig
   end) ->
   struct
    module H = ReadHistory.Make(V)(D)(U)(S)(M)(Features)(DL)(UL)(SL)(ML)

    module P = H.P

    module R = H.R

    (** val cell_changed : R.state -> R.state -> V.t -> V.t -> bool **)

    let cell_changed before after source target =
      negb
        (R.equivalent (R.stored_contribution before source target)
          (R.stored_contribution after source target))

    (** val requeue_source : R.state -> R.state -> V.t -> V.t -> R.state **)

    let requeue_source before after source target =
      if cell_changed before after source target
      then R.enqueue after source
      else after

    (** val finish_write :
        R.state -> R.state -> R.frame -> V.t -> bool -> R.state **)

    let finish_write before after fr target aggregate_changed =
      let next = requeue_source before after (R.frame_owner fr) target in
      if aggregate_changed then R.enqueue next target else next

    (** val publish : V.t list -> R.state -> R.frame -> R.state **)

    let rec publish targets st fr =
      match targets with
      | [] -> st
      | target :: rest ->
        let input0 =
          match M.lookup (R.frame_local_side fr) target with
          | Some value -> value
          | None -> D.bottom
        in
        let (next, changed) = R.write_side_contribution st fr target input0 in
        publish rest (finish_write st next fr target changed) fr

    (** val next_config :
        H.P.R.ConstraintSystem.system -> R.config -> H.P.R.config option **)

    let next_config tf c =
      let st = R.cfg_state c in
      (match R.cfg_control c with
       | R.RunDead (fr, direct, l, k) ->
         (match l with
          | [] ->
            Some { R.cfg_state =
              (R.publish_targets
                (publish (S.elements (R.frame_current_targets fr)) st fr) fr);
              R.cfg_control = (R.RunCommit (fr, direct, k)) }
          | target :: rest ->
            if S.mem target (R.frame_current_targets fr)
            then Some { R.cfg_state = st; R.cfg_control = (R.RunDead (fr,
                   direct, rest, k)) }
            else let (next, changed) =
                   R.write_side_contribution st fr target D.bottom
                 in
                 Some
                 (R.continue_dead
                   (requeue_source st next (R.frame_owner fr) target) fr
                   direct target rest k changed))
       | _ -> H.P.next_fresh tf c)

    (** val run_fuel :
        int -> H.P.R.ConstraintSystem.system -> R.config -> R.config **)

    let rec run_fuel fuel tf c =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> c)
        (fun fuel0 ->
        match next_config tf c with
        | Some next -> run_fuel fuel0 tf next
        | None -> c)
        fuel

    (** val solve_fuel :
        int -> H.P.R.ConstraintSystem.system -> V.t list -> R.state option **)

    let solve_fuel fuel tf roots =
      R.terminal_state (run_fuel fuel tf (R.initial_config roots))
   end
 end

module PublicationStability =
 struct
  module Make =
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
   functor (Features:FEATURES) ->
   functor (DL:sig
   end) ->
   functor (UL:sig
    val remaining_changes : U.phase -> D.t -> int
   end) ->
   functor (SL:sig
   end) ->
   functor (ML:sig
   end) ->
   struct
    module C = CellRepair.Make(V)(D)(U)(S)(M)(Features)(DL)(UL)(SL)(ML)
   end
 end

module Make =
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
 functor (Features:FEATURES) ->
 functor (DL:sig
 end) ->
 functor (UL:sig
  val remaining_changes : U.phase -> D.t -> int
 end) ->
 functor (SL:sig
 end) ->
 functor (ML:sig
 end) ->
 struct
  module PS =
   PublicationStability.Make(V)(D)(U)(S)(M)(Features)(DL)(UL)(SL)(ML)

  module R = PS.C.R

  (** val input : R.frame -> V.t -> D.t **)

  let input fr target =
    match M.lookup (R.frame_local_side fr) target with
    | Some value -> value
    | None -> D.bottom

  module Sem = PS.C.H.B.Sem

  module O = Sem.Observation

  module Demand =
   struct
    (** val prepend :
        (V.t * D.t) list -> (V.t * D.t) list -> V.t list -> O.observation ->
        O.observation **)

    let prepend reads effects spawns result =
      { O.observed_direct = (O.observed_direct result); O.observed_reads =
        (app reads (O.observed_reads result)); O.observed_sides =
        (app effects (O.observed_sides result)); O.observed_spawns =
        (app spawns (O.observed_spawns result)) }
   end

  module Readers =
   struct
   end

  module Support =
   struct
    (** val finite_bridge :
        Sem.ConstraintSyntax.system -> V.t list -> Sem.finite_system ->
        PS.C.H.B.Sem.finite_system **)

    let finite_bridge =
      Sem.support
   end

  module SourceCredit =
   struct
    (** val credit : V.t list -> PS.C.H.B.R.state -> V.t -> int **)

    let credit =
      PS.C.H.B.Credits.source_side_credit

    (** val charge : V.t list -> V.t -> R.config -> R.config -> int **)

    let charge support0 source before after =
      if Nat.ltb (credit support0 (R.cfg_state after) source)
           (credit support0 (R.cfg_state before) source)
      then Stdlib.Int.succ 0
      else 0

    (** val active_run :
        int -> V.t list -> PS.C.H.P.R.ConstraintSystem.system -> V.t ->
        R.config -> R.config * int **)

    let rec active_run fuel support0 tf source c =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> (c, 0))
        (fun rest ->
        match PS.C.next_config tf c with
        | Some next ->
          if PS.C.H.T.control_containsb source (R.cfg_control next)
          then let (last, count) = active_run rest support0 tf source next in
               (last, (add (charge support0 source c next) count))
          else (c, 0)
        | None -> (c, 0))
        fuel
   end

  module RankedResets =
   struct
   end

  module TargetCredit =
   struct
    (** val credit : V.t list -> PS.C.H.B.R.state -> V.t -> int **)

    let credit =
      PS.C.H.T.target_side_credit

    (** val charge : V.t list -> V.t -> R.config -> R.config -> int **)

    let charge support0 root before after =
      if Nat.ltb (credit support0 (R.cfg_state after) root)
           (credit support0 (R.cfg_state before) root)
      then Stdlib.Int.succ 0
      else 0

    (** val active_run :
        int -> V.t list -> PS.C.H.P.R.ConstraintSystem.system -> V.t ->
        R.config -> R.config * int **)

    let rec active_run fuel support0 tf root c =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> (c, 0))
        (fun rest ->
        match PS.C.next_config tf c with
        | Some next ->
          if PS.C.H.T.control_containsb root (R.cfg_control next)
          then let (last, count) = active_run rest support0 tf root next in
               (last, (add (charge support0 root c next) count))
          else (c, 0)
        | None -> (c, 0))
        fuel
   end

  module Episodes =
   struct
   end

  module MaterializationBudget =
   struct
    (** val credit : V.t list -> PS.C.H.B.R.state -> int **)

    let credit =
      PS.C.H.T.unmaterialized_count
   end

  module Promotion =
   struct
   end

  module OrdinaryCredit =
   struct
    (** val credit : R.config -> V.t -> int **)

    let credit c owner =
      PS.C.H.T.active_ordinary_credit (R.cfg_state c) (R.cfg_control c) owner

    (** val charge : R.config -> R.config -> V.t -> int **)

    let charge before after owner =
      if Nat.ltb (credit after owner) (credit before owner)
      then Stdlib.Int.succ 0
      else 0

    (** val active_run :
        int -> PS.C.H.P.R.ConstraintSystem.system -> V.t -> R.config ->
        R.config * int **)

    let rec active_run fuel tf owner c =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> (c, 0))
        (fun rest ->
        match PS.C.next_config tf c with
        | Some next ->
          if PS.C.H.T.control_containsb owner (R.cfg_control next)
          then let (last, count) = active_run rest tf owner next in
               (last, (add (charge c next owner) count))
          else (c, 0)
        | None -> (c, 0))
        fuel
   end

  module PendingBudget =
   struct
    (** val entry : R.state -> V.t -> V.t -> int **)

    let entry st owner target =
      if R.rank_lt st owner target
      then (match R.Ranking.lookup (R.ranking st) target with
            | Some rank -> Stdlib.Int.succ rank
            | None -> 0)
      else 0

    (** val total : R.state -> V.t -> V.t list -> int **)

    let total st owner pending =
      fold_right (fun target n -> Nat.max (entry st owner target) n) 0 pending

    (** val credit : R.state -> V.t -> int **)

    let credit st owner =
      total st owner (R.queue st)
   end

  module EvaluationQueue =
   struct
   end

  module EvaluationReads =
   struct
   end

  module EvaluationPrefix =
   struct
   end

  module FirstCommit =
   struct
   end

  module RoundAccounts =
   struct
   end

  module EpisodePath =
   struct
   end

  module ActiveAccounts =
   struct
   end

  module HigherRetry =
   struct
    (** val resumed :
        (V.t -> R.ConstraintSystem.rhs) -> R.state -> PS.C.H.P.R.state ->
        R.frame -> R.continuation -> Sem.R.config **)

    let resumed tf saved current fr k =
      { Sem.R.cfg_state = (PS.C.H.P.clear_owner current (R.frame_owner fr));
        Sem.R.cfg_control = (R.RunRhs
        ((R.fresh_frame saved (R.frame_owner fr) (R.frame_phase fr)),
        (tf (R.frame_owner fr)), k)) }
   end

  module RetryMeasure =
   struct
    (** val vector :
        V.t list -> V.t -> R.config ->
        int * (int * (int * (int * (int * int)))) **)

    let vector support0 owner c =
      ((MaterializationBudget.credit support0 (R.cfg_state c)),
        ((PS.C.H.T.promotion_reserve (R.cfg_state c) owner),
        ((SourceCredit.credit support0 (R.cfg_state c) owner),
        ((TargetCredit.credit support0 (R.cfg_state c) owner),
        ((OrdinaryCredit.credit c owner),
        (PendingBudget.credit (R.cfg_state c) owner))))))
   end

  module RoundComposition =
   struct
   end

  module ReaderRanks =
   struct
   end

  module Draining =
   struct
   end

  module CommitQueues =
   struct
   end

  module DrainMeasure =
   struct
   end

  module RoundResult =
   struct
   end

  module OrdinaryRound =
   struct
   end

  module CompleteRound =
   struct
   end

  module EpisodeTermination =
   struct
   end

  module Termination =
   struct
    (** val loop_control : V.t list option -> R.control **)

    let loop_control = function
    | Some pending -> R.RunSeedLoop pending
    | None -> R.RunLoop

    (** val loop_continuation : V.t list option -> R.continuation **)

    let loop_continuation = function
    | Some pending -> R.KSeedLoop pending
    | None -> R.KLoop

    (** val loop_done : V.t list option -> R.control **)

    let loop_done = function
    | Some pending -> R.RunSeeds pending
    | None -> R.RunLoop
   end
 end

module Coq_Make =
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
 functor (Features:FEATURES) ->
 functor (DL:sig
 end) ->
 functor (UL:sig
  val remaining_changes : U.phase -> D.t -> int
 end) ->
 functor (SL:sig
 end) ->
 functor (ML:sig
 end) ->
 struct
  module O = Make(V)(D)(U)(S)(M)(Features)(DL)(UL)(SL)(ML)

  module C = O.PS.C

  module P = C.P

  module R = C.R

  module B = C.H.B

  module H = C.H

  (** val next_config :
      C.H.P.R.ConstraintSystem.system -> R.config -> C.H.P.R.config option **)

  let next_config tf c =
    match R.cfg_control c with
    | R.Return c0 ->
      (match c0 with
       | R.KAfterSide (fr, _, k) ->
         (match P.pending_above (R.cfg_state c) (R.frame_owner fr) with
          | Some p ->
            let (target, rest) = p in
            Some (P.suspend_commit tf (R.cfg_state c) fr k target rest)
          | None -> C.next_config tf c)
       | _ -> C.next_config tf c)
    | _ -> C.next_config tf c

  (** val run_fuel :
      int -> C.H.P.R.ConstraintSystem.system -> R.config -> R.config **)

  let rec run_fuel fuel tf c =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> c)
      (fun fuel0 ->
      match next_config tf c with
      | Some next -> run_fuel fuel0 tf next
      | None -> c)
      fuel

  (** val solve_fuel :
      int -> C.H.P.R.ConstraintSystem.system -> V.t list -> R.state option **)

  let solve_fuel fuel tf roots =
    R.terminal_state (run_fuel fuel tf (R.initial_config roots))
 end

module Solver = Coq_Make
