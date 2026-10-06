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

module Narrowing_fixed_point : sig
  module Make_with_features (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) (Features : FEATURES) :
    SOLVER with type variable = V.t and type value = D.t
  module Make (V : VAR) (D : DOMAIN)
    (U : UPDATE with type variable = V.t and type value = D.t) :
    SOLVER with type variable = V.t and type value = D.t
end
