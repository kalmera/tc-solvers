open Interfaces

module Simple : sig
  module Make (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) :
    SOLVER with type variable = V.t and type value = D.t
end

module Restarting : sig
  module Make (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) (Features : FEATURES) :
    SOLVER with type variable = V.t and type value = D.t
end

module Plus_restarting : sig
  (* All four policies enabled. Clients can supply their own feature module. *)
  module Default_features : PLUS_FEATURES
  module Make_with_features (V : ORDERED_VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t)
    (SU : SIDE_UPDATE with type variable = V.t and type value = D.t)
    (Features : PLUS_FEATURES) :
    PLUS_SOLVER with type variable = V.t and type value = D.t
  module Make (V : ORDERED_VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t)
    (SU : SIDE_UPDATE with type variable = V.t and type value = D.t) :
    PLUS_SOLVER with type variable = V.t and type value = D.t
end

module Narrowing_fixed_point : sig
  module Make_with_features (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) (Features : FEATURES) :
    SOLVER with type variable = V.t and type value = D.t
  module Make (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) :
    SOLVER with type variable = V.t and type value = D.t
end
