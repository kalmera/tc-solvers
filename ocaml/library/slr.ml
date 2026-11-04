open Interfaces

module Simple = struct
  module Make (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) = struct
    type variable = V.t
    type value = D.t
    type rhs = (variable -> value) -> (variable -> value -> unit) ->
      (variable -> unit) -> value
    type system = variable -> rhs option
    module H = Core_common.Table (V)
    type solution = value H.t
    let value solution variable = H.find_default solution variable D.bottom
    let mem = H.mem
    let iter = H.iter
    let solve ?(initial = []) system roots =
      let module S = struct
        type v = V.t
        type d = D.t
        module Var = V
        module Dom = struct
          include D
          let bot () = D.bottom
          let equal left right = D.leq left right && D.leq right left
        end
        let system = system
      end in
      let module Engine = Core_simple.Make (Core_simple.Control) (S) (U) (H) in
      Engine.solve initial roots
  end
end

module Restarting = struct
  module Make (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) (Features : FEATURES) = struct
    type variable = V.t
    type value = D.t
    type rhs = (variable -> value) -> (variable -> value -> unit) ->
      (variable -> unit) -> value
    type system = variable -> rhs option
    module H = Core_common.Table (V)
    type solution = value H.t
    let value solution variable = H.find_default solution variable D.bottom
    let mem = H.mem
    let iter = H.iter
    let solve ?(initial = []) system roots =
      let module S = struct
        type v = V.t
        type d = D.t
        module Var = V
        module Dom = struct
          include D
          let bot () = D.bottom
          let equal left right = D.leq left right && D.leq right left
        end
        let system = system
      end in
      let module Engine = Core_restarting.Make (Core_restarting.Control) (Features) (S) (U) (H) in
      Engine.solve initial roots
  end
end

module Narrowing_fixed_point = struct
  module Make_with_features (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) (Features : FEATURES) = struct
    type variable = V.t
    type value = D.t
    type rhs = (variable -> value) -> (variable -> value -> unit) ->
      (variable -> unit) -> value
    type system = variable -> rhs option
    module H = Core_common.Table (V)
    type solution = value H.t
    let value solution variable = H.find_default solution variable D.bottom
    let mem = H.mem
    let iter = H.iter
    let solve ?(initial = []) system roots =
      let module S = struct
        type v = V.t
        type d = D.t
        module Var = V
        module Dom = struct
          include D
          let bot () = D.bottom
          let equal left right = D.leq left right && D.leq right left
        end
        let system = system
      end in
      let module Engine = Core_narrowing_fixed_point.Make (Core_narrowing_fixed_point.Control) (Features) (S) (U) (H) in
      Engine.solve initial roots
  end
  module Make (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) =
    Make_with_features (V) (D) (U) (Core_narrowing_fixed_point.Features)
end

module Plus_restarting = struct
  module Default_features = struct
    let side_effect_phase_reset = true
    let dead_side_elimination = true
    let recompute_controlled = true
    let defer_spawns = true
  end

  module Make_with_features (V : ORDERED_VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t)
    (SU : SIDE_UPDATE with type variable = V.t and type value = D.t)
    (Features : PLUS_FEATURES) = struct
    type variable = V.t
    type value = D.t
    type rhs =
      | Ret of value
      | Get of variable * (value -> rhs)
      | Side of variable * value * rhs
      | Spawn of variable * rhs
    type system = variable -> rhs
    type event = (variable, value) Interfaces.event
    type event_envelope = (variable, value) Interfaces.event_envelope
    module Ordered = struct type t = V.t let compare = V.compare end
    module Store = Map.Make (Ordered)
    module Keys = Set.Make (Ordered)
    type solution = { values : value Store.t; completion : completion; statistics : statistics }
    let value solution variable =
      match Store.find_opt variable solution.values with Some value -> value | None -> D.bottom
    let mem solution variable = Store.mem variable solution.values
    let iter visit solution = Store.iter visit solution.values
    let bindings solution = Store.bindings solution.values
    let completion solution = solution.completion
    let statistics solution = solution.statistics

    let solve ?on_event ?(max_steps = max_int) system roots =
      if max_steps < 0 then invalid_arg "SLR-TC+: negative step limit";
      let observer_errors = ref 0 in
      let current_transition = ref 0 in
      let module Variables = struct type t = V.t let eq_dec = V.equal let hash = V.hash end in
      let module Sets = struct
        type t = Keys.t
        let empty = Keys.empty
        let mem = Keys.mem
        let add = Keys.add
        let elements = Keys.elements
      end in
      let module Maps = struct
        type 'a t = 'a Store.t
        let empty = Store.empty
        let lookup map key = Store.find_opt key map
        let update map key value = Store.add key value map
        let values map = List.map snd (Store.bindings map)
      end in
      let module Flags = struct
        let recompute_controlled = Features.recompute_controlled
        let defer_spawns = Features.defer_spawns
        let restart_side_phases = Features.side_effect_phase_reset
        let eliminate_dead_sides = Features.dead_side_elimination
      end in
      let module Observe = struct
        let enabled = Option.is_some on_event
        let emit event =
          match on_event with
          | None -> ()
          | Some callback ->
            try callback { transition = !current_transition; event }
            with _ -> incr observer_errors
      end in
      (* The generative application owns every mutable rank, queue and FIFO.
         Repeated and nested solves never share these objects. *)
      let module Engine = Core_plus_restarting.Make (Variables) (D) (U) (SU) (Sets) (Maps) (Flags) (Observe) in
      let module R = Engine.ConstraintSystem in
      let rec convert = function
        | Ret value -> R.Ret value
        | Get (target, next) -> R.Get (target, fun value -> convert (next value))
        | Side (target, value, next) -> R.Side (target, value, convert next)
        | Spawn (target, next) -> R.Spawn (target, convert next)
      in
      let system owner = convert (system owner) in
      let rec run steps config =
        match Engine.terminal_state config with
        | Some state -> steps, state, Complete
        | None when steps = max_steps -> steps, config.Engine.cfg_state, Step_limit
        | None ->
          if Observe.enabled then current_transition := steps;
          match Engine.next_config system config with
          | Some next -> run (steps + 1) next
          | None -> failwith "SLR-TC+: stopped before terminal control"
      in
      let steps, state, completion = run 0 (Engine.initial_config roots) in
      { values = state.Engine.sigma; completion;
        statistics = { steps; evaluations = !(Engine.evaluations);
          discoveries = Engine.Ranking.size state.Engine.ranking;
          observer_errors = !observer_errors } }
  end

  module Make (V : ORDERED_VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t)
    (SU : SIDE_UPDATE with type variable = V.t and type value = D.t) =
    Make_with_features (V) (D) (U) (SU) (Default_features)
end
