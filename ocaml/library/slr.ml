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
