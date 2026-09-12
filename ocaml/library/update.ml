open Interfaces

module Box (V : VAR) (D : BOX_DOMAIN) = struct
  type variable = V.t
  type value = D.t
  type phase = Copy of int | W | N | F
  let widen old input = D.widen old (D.join old input)
  let update _is_side _variable phase old input =
    match phase with
    | Copy n -> (if n = 0 then W else Copy (n - 1)), input
    | W | N ->
        if D.leq input old then N, D.narrow old input
        else (if phase = N then F else W), widen old input
    | F -> F, widen old input
end

module TwoCopy (V : VAR) (D : BOX_DOMAIN) = struct
  include Box (V) (D)
  let initial_phase _ _ = Copy 1
end

module WidenNarrow (V : VAR) (D : BOX_DOMAIN) = struct
  include Box (V) (D)
  let initial_phase _ _ = W
end

module Join (V : VAR) (D : DOMAIN) = struct
  type variable = V.t
  type value = D.t
  type phase = unit
  let initial_phase _ _ = ()
  let update _ _ () old input = (), D.join old input
end
