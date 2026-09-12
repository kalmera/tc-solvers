module V = struct
  type t = int
  let equal = Int.equal
  let hash = Hashtbl.hash
end

(* A finite chain, with widening to top and gradual narrowing. *)
module D = struct
  type t = int
  let bottom = 0
  let join = max
  let leq = ( <= )
  let widen _ _ = 5
  let narrow old input = max input (old - 1)
end
