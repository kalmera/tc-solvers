module V = struct type t = int let eq_dec = Int.equal end
module D = struct
  type t = Bottom | One | Two
  let rank = function Bottom -> 0 | One -> 1 | Two -> 2
  let bottom = Bottom
  let leq x y = rank x <= rank y
  let join x y = if leq x y then y else x
end
module WN = struct
  (* Finite-height widening and exact narrowing make the combined update
     value-idempotent, including across phase changes. *)
  let widen = D.join
  let narrow _ input = input
end
module Set = struct
  type t = int list
  let empty = []
  let mem = List.mem
  let add x xs = if mem x xs then xs else x :: xs
  let elements xs = xs
end
module Map = struct
  type 'a t = (int * 'a) list
  let empty = []
  let lookup xs x = List.assoc_opt x xs
  let update xs x v = (x, v) :: List.remove_assoc x xs
  let values entries = List.map snd entries
end
module U = struct
  type phase = W | N | F
  let initial_phase _ _ = W
  let update _ _ phase old input = match phase with
    | W | N -> if D.leq input old then N, WN.narrow old input
      else (if phase=N then F else W), WN.widen old (D.join old input)
    | F -> F, WN.widen old (D.join old input)
end
module Flags = struct let restart_side_phases = true let eliminate_dead_sides = true end
(* Finite-height credits reserve room for narrowing and fallback phases. *)
module Credit = struct
  let remaining_changes phase value = match phase with
    | U.W -> 8 - D.rank value
    | U.N -> 3 + D.rank value
    | U.F -> 2 - D.rank value
end
module Empty = struct end

module Solver = Tc_solvers_extracted_narrowing_fixed_point.NarrowingFixedPointRuntime.Solver
  (V) (D) (U) (Set) (Map) (Flags) (Empty) (Credit) (Empty) (Empty)
module R = Solver.R
let system = function
  | 0 -> R.ConstraintSystem.Side (1, D.Two, R.ConstraintSystem.Ret D.One)
  | _ -> R.ConstraintSystem.Ret D.Bottom
let () =
  match Solver.solve_fuel 1000 system [0] with
  | None -> failwith "Narrowing Fixed Point exhausted example fuel"
  | Some final ->
      assert (R.sigma_value final 0 = D.One);
      assert (R.sigma_value final 1 = D.Two);
      print_endline "Narrowing Fixed Point: owner 0 = 1; side target 1 = 2"
