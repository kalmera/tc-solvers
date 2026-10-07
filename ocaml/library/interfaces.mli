module type VAR = Hashtbl.HashedType

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

module type SOLVER = sig
  type variable
  type value
  type rhs = (variable -> value) -> (variable -> value -> unit) ->
    (variable -> unit) -> value
  type system = variable -> rhs option
  type solution

  (** Fresh solve; repeated initial contributions are joined and retained.
      Callback and system-lookup exceptions propagate. *)
  val solve : ?initial:(variable * value) list -> system -> variable list -> solution

  (** Bottom when absent. *)
  val value : solution -> variable -> value

  (** Whether the variable has a stored binding, including stored bottom. *)
  val mem : solution -> variable -> bool

  (** Visit each stored binding once, in unspecified order. *)
  val iter : (variable -> value -> unit) -> solution -> unit
end
