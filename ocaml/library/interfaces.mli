module type VAR = Hashtbl.HashedType

(* [compare x y = 0] must agree with [equal x y]. Ordering is used for
   reference-compatible reader, contribution and dead-target traversal. *)
module type ORDERED_VAR = sig
  include VAR
  val compare : t -> t -> int
end

module type DOMAIN = sig
  type t
  val bottom : t
  val join : t -> t -> t
  val leq : t -> t -> bool
end

module type BOX_DOMAIN = sig
  include DOMAIN
  val widen : t -> t -> t
  val narrow : t -> t -> t
end

module type UPDATE = sig
  type variable
  type value
  type phase
  val initial_phase : bool -> variable -> phase
  val update : bool -> variable -> phase -> value -> value -> phase * value
end

module type FEATURES = sig
  val side_effect_phase_reset : bool
  val dead_side_elimination : bool
  val recompute_controlled : bool
end

module type PLUS_FEATURES = sig
  include FEATURES
  val defer_spawns : bool
end

(* Side policies have their own phase and see the old incoming aggregate. *)
module type SIDE_UPDATE = sig
  type variable
  type value
  type phase
  (* Source and target, respectively. *)
  val initial_phase : variable -> variable -> phase
  (* Source, target, phase, old contribution, cumulative input, aggregate. *)
  val update : variable -> variable -> phase -> value -> value -> value -> phase * value
end

type ('variable, 'value) event =
  | Evaluation_start of 'variable
  | Evaluation_result of 'variable * 'value
  | Read_request of { owner : 'variable; target : 'variable }
  | Read of { owner : 'variable; target : 'variable; value : 'value }
  | Side of { owner : 'variable; target : 'variable; value : 'value }
  | Spawn of { owner : 'variable; target : 'variable }
  | Discover of { variable : 'variable; rank : int }
  | Materialize of { variable : 'variable; value : 'value }
  | Value_change of { variable : 'variable; old_value : 'value; value : 'value }
  | Side_update of {
      source : 'variable; target : 'variable; input : 'value;
      old_value : 'value; value : 'value;
    }

(* Zero-based index of the reference transition producing the event. Several
   events may share an index and are delivered in callback order. A budget N
   permits only indices 0 through N-1; no event is emitted for an unexecuted
   transition. [Read_request] precedes target resolution; [Read] completes it. *)
type ('variable, 'value) event_envelope = {
  transition : int;
  event : ('variable, 'value) event;
}

type completion = Complete | Step_limit
type statistics = {
  steps : int;
  evaluations : int;
  discoveries : int;
  observer_errors : int;
}

module type PLUS_SOLVER = sig
  type variable
  type value
  type rhs =
    | Ret of value
    | Get of variable * (value -> rhs)
    | Side of variable * value * rhs
    | Spawn of variable * rhs
  type system = variable -> rhs
  type nonrec event = (variable, value) event
  type nonrec event_envelope = (variable, value) event_envelope
  type solution

  (* [max_steps] counts reference-machine transitions. A limit returns a
     marked partial solution. Observers run synchronously, are never retained,
     and receive every event regardless of client-side trace retention.
     Observer exceptions are counted and isolated; solver exceptions propagate. *)
  (* [aggregate_cache] defaults to false. Enabling it requires a lawful join
     semilattice modulo mutual [leq], with bottom as identity. Domain operations,
     transfer continuations and policies (including phase transitions) must
     respect that equivalence. Aggregate representatives and join-call counts
     may differ from the full fold; event order and scheduling are preserved. *)
  val solve : ?aggregate_cache:bool -> ?on_event:(event_envelope -> unit) ->
    ?max_steps:int -> system -> variable list -> solution
  val value : solution -> variable -> value
  val mem : solution -> variable -> bool
  val iter : (variable -> value -> unit) -> solution -> unit
  (* Ordered snapshot; values are shared and must be immutable. *)
  val bindings : solution -> (variable * value) list
  val completion : solution -> completion
  val statistics : solution -> statistics
end

module type SOLVER = sig
  type variable
  type value
  type rhs = (variable -> value) -> (variable -> value -> unit) ->
    (variable -> unit) -> value
  type system = variable -> rhs option
  type solution

  (* Fresh solve; repeated initial contributions are joined and retained.
      Callback and system-lookup exceptions propagate. *)
  val solve : ?initial:(variable * value) list -> system -> variable list -> solution

  (* Bottom when absent. *)
  val value : solution -> variable -> value

  (* Whether the variable has a stored binding, including stored bottom. *)
  val mem : solution -> variable -> bool

  (* Visit each stored binding once, in unspecified order. *)
  val iter : (variable -> value -> unit) -> solution -> unit
end
